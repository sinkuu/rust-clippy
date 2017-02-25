use rustc::hir::*;
use rustc::hir::intravisit::FnKind;
use rustc::hir::def_id::DefId;
use rustc::lint::*;
use rustc::ty::{self, TypeFoldable};
use rustc::traits;
use rustc::middle::expr_use_visitor as euv;
use rustc::middle::mem_categorization as mc;
use syntax::ast::NodeId;
use syntax_pos::Span;
use syntax::errors::DiagnosticBuilder;
use utils::{in_macro, is_self, is_copy, implements_trait, match_type, snippet, span_lint_and_then,
            multispan_sugg, paths};
use std::collections::{HashSet, HashMap};

/// **What it does:** Checks for functions taking arguments by value, but not consuming them in its
/// body.
///
/// **Why is this bad?** Taking arguments by reference is more flexible and can sometimes avoid
/// unnecessary allocations.
///
/// **Known problems:** Hopefully none.
///
/// **Example:**
/// ```rust
/// fn foo(v: Vec<i32>) {
///     assert_eq!(v.len(), 42);
/// }
/// ```
declare_lint! {
    pub NEEDLESS_PASS_BY_VALUE,
    Warn,
    "functions taking arguments by value, but not consuming them in its body"
}

pub struct NeedlessPassByValue;

impl LintPass for NeedlessPassByValue {
    fn get_lints(&self) -> LintArray {
        lint_array![NEEDLESS_PASS_BY_VALUE]
    }
}

impl<'a, 'tcx> LateLintPass<'a, 'tcx> for NeedlessPassByValue {
    fn check_fn(
        &mut self,
        cx: &LateContext<'a, 'tcx>,
        kind: FnKind<'tcx>,
        decl: &'tcx FnDecl,
        body: &'tcx Body,
        span: Span,
        node_id: NodeId
    ) {
        if in_macro(cx, span) {
            return;
        }

        if !matches!(kind, FnKind::ItemFn(..)) {
            return;
        }

        // Allows these to be passed by value.
        let fn_trait = cx.tcx.lang_items.fn_trait().expect("failed to find `Fn` trait");
        //let borrow_trait = get_trait_def_id(cx, &paths::BORROW_TRAIT).expect("failed to find `Borrow` trait");

        let preds: Vec<ty::TraitPredicate> = {
            let parameter_env = ty::ParameterEnvironment::for_item(cx.tcx, node_id);
            traits::elaborate_predicates(cx.tcx, parameter_env.caller_bounds.clone())
                .filter(|p| !p.is_global())
                .filter_map(|pred| if let ty::Predicate::Trait(ty::Binder(trait_ref)) = pred {
                    Some(trait_ref)
                } else {
                    None
                })
                .collect()
        };

        // Collect moved variables and spans which will need dereferencings from the function body.
        let MovedVariablesCtxt { moved_vars, spans_need_deref, .. } = {
            let mut ctx = MovedVariablesCtxt::new(cx);
            let infcx = cx.tcx.borrowck_fake_infer_ctxt(body.id());
            {
                let mut v = euv::ExprUseVisitor::new(&mut ctx, &infcx);
                v.consume_body(body);
            }
            ctx
        };

        let fn_def_id = cx.tcx.hir.local_def_id(node_id);
        let param_env = ty::ParameterEnvironment::for_item(cx.tcx, node_id);
        let fn_sig = cx.tcx.item_type(fn_def_id).fn_sig();
        let fn_sig = cx.tcx.liberate_late_bound_regions(param_env.free_id_outlive, fn_sig);

        for ((input, ty), arg) in decl.inputs.iter().zip(fn_sig.inputs()).zip(&body.arguments) {
            if_let_chain! {[
                !is_self(arg),
                !ty.is_mutable_pointer(),
                !is_copy(cx, ty, node_id),
                !implements_trait(cx, ty, fn_trait, &[], Some(node_id)),
                // !implements_trait(cx, ty, asref_trait, &[], Some(node_id)),

                let PatKind::Binding(mode, defid, ..) = arg.pat.node,
                !moved_vars.contains(&defid),

                // Give up if `ty` implements a trait which is also implemented for some `&T`.
                !preds.iter()
                    .filter(|tpred| &tpred.self_ty() == ty)
                    .any(|tpred| is_trait_implemented_for_ref(cx, tpred.def_id())),
            ], {
                let m = match mode {
                    BindingMode::BindByRef(m) | BindingMode::BindByValue(m) => m,
                };
                if m == Mutability::MutMutable {
                    continue;
                }

                // Suggestion logic
                let sugg = |db: &mut DiagnosticBuilder| {
                    let deref_span = spans_need_deref.get(&defid);
                    if_let_chain! {[
                        match_type(cx, ty, &paths::VEC),
                        let TyPath(QPath::Resolved(_, ref path)) = input.node,
                        let Some(elem_ty) = path.segments.iter()
                            .find(|seg| &*seg.name.as_str() == "Vec")
                            .map(|ps| ps.parameters.types()[0]),
                    ], {
                        let slice_ty = format!("&[{}]", snippet(cx, elem_ty.span, "_"));
                        db.span_suggestion(input.span,
                                        &format!("consider changing the type to `{}`", slice_ty),
                                        slice_ty);
                        assert!(deref_span.is_none());
                        return; // `Vec` and `String` cannot be destructured - no need for `*` suggestion
                    }}

                    if match_type(cx, ty, &paths::STRING) {
                        db.span_suggestion(input.span,
                                           "consider changing the type to `&str`",
                                           "&str".to_string());
                        assert!(deref_span.is_none());
                        return;
                    }

                    let mut spans = vec![(input.span, format!("&{}", snippet(cx, input.span, "_")))];

                    // Suggests adding `*` to dereference the added reference.
                    if let Some(deref_span) = deref_span {
                        spans.extend(deref_span.iter().cloned()
                                     .map(|span| (span, format!("*{}", snippet(cx, span, "<expr>")))));
                        spans.sort_by_key(|&(span, _)| span);
                    }
                    multispan_sugg(db, "consider taking a reference instead".to_string(), spans);
                };

                span_lint_and_then(cx,
                          NEEDLESS_PASS_BY_VALUE,
                          input.span,
                          "this argument is passed by value, but not consumed in the function body",
                          sugg);
            }}
        }
    }
}

struct MovedVariablesCtxt<'a, 'tcx: 'a> {
    cx: &'a LateContext<'a, 'tcx>,
    moved_vars: HashSet<DefId>,
    /// Spans which need to be prefixed with `*` for dereferencing the suggested additional
    /// reference.
    spans_need_deref: HashMap<DefId, HashSet<Span>>,
}

impl<'a, 'tcx: 'a> MovedVariablesCtxt<'a, 'tcx> {
    fn new(cx: &'a LateContext<'a, 'tcx>) -> Self {
        MovedVariablesCtxt {
            cx: cx,
            moved_vars: HashSet::new(),
            spans_need_deref: HashMap::new(),
        }
    }

    fn move_common(&mut self, _consume_id: NodeId, _span: Span, cmt: mc::cmt<'tcx>) {
        let cmt = unwrap_downcast_or_interior(cmt);

        if_let_chain! {[
            let mc::Categorization::Local(vid) = cmt.cat,
            let Some(def_id) = self.cx.tcx.hir.opt_local_def_id(vid),
        ], {
                self.moved_vars.insert(def_id);
        }}
    }

    fn non_moving_pat(&mut self, matched_pat: &Pat, cmt: mc::cmt<'tcx>) {
        let cmt = unwrap_downcast_or_interior(cmt);

        if_let_chain! {[
            let mc::Categorization::Local(vid) = cmt.cat,
            let Some(def_id) = self.cx.tcx.hir.opt_local_def_id(vid),
        ], {
            let mut id = matched_pat.id;
            loop {
                let parent = self.cx.tcx.hir.get_parent_node(id);
                if id == parent {
                    // no parent
                    return;
                }
                id = parent;

                if let Some(node) = self.cx.tcx.hir.find(id) {
                    match node {
                        map::Node::NodeExpr(e) => {
                            // `match` and `if let`
                            if let ExprMatch(ref c, ..) = e.node {
                                self.spans_need_deref
                                    .entry(def_id)
                                    .or_insert_with(HashSet::new)
                                    .insert(c.span);
                            }
                        }

                        map::Node::NodeStmt(s) => {
                            // `let <pat> = x;`
                            if_let_chain! {[
                                let StmtDecl(ref decl, _) = s.node,
                                let DeclLocal(ref local) = decl.node,
                            ], {
                                self.spans_need_deref
                                    .entry(def_id)
                                    .or_insert_with(HashSet::new)
                                    .insert(local.init
                                        .as_ref()
                                        .map(|e| e.span)
                                        .expect("`let` stmt without init aren't caught by match_pat"));
                            }}
                        }

                        _ => {}
                    }
                }
            }
        }}
    }
}

impl<'a, 'tcx: 'a> euv::Delegate<'tcx> for MovedVariablesCtxt<'a, 'tcx> {
    fn consume(&mut self, consume_id: NodeId, consume_span: Span, cmt: mc::cmt<'tcx>, mode: euv::ConsumeMode) {
        if let euv::ConsumeMode::Move(_) = mode {
            self.move_common(consume_id, consume_span, cmt);
        }
    }

    fn matched_pat(&mut self, matched_pat: &Pat, cmt: mc::cmt<'tcx>, mode: euv::MatchMode) {
        if let euv::MatchMode::MovingMatch = mode {
            self.move_common(matched_pat.id, matched_pat.span, cmt);
        } else {
            self.non_moving_pat(matched_pat, cmt);
        }
    }

    fn consume_pat(&mut self, consume_pat: &Pat, cmt: mc::cmt<'tcx>, mode: euv::ConsumeMode) {
        if let euv::ConsumeMode::Move(_) = mode {
            self.move_common(consume_pat.id, consume_pat.span, cmt);
        }
    }

    fn borrow(
        &mut self,
        _: NodeId,
        _: Span,
        _: mc::cmt<'tcx>,
        _: &'tcx ty::Region,
        _: ty::BorrowKind,
        _: euv::LoanCause
    ) {
    }

    fn mutate(&mut self, _: NodeId, _: Span, _: mc::cmt<'tcx>, _: euv::MutateMode) {}

    fn decl_without_init(&mut self, _: NodeId, _: Span) {}
}


fn unwrap_downcast_or_interior(mut cmt: mc::cmt) -> mc::cmt {
    loop {
        match cmt.cat.clone() {
            mc::Categorization::Downcast(c, _) |
            mc::Categorization::Interior(c, _) => {
                cmt = c;
            },
            _ => return cmt,
        }
    }
}

/// Checks if given trait is implemented for `&T`.
fn is_trait_implemented_for_ref<'a, 'tcx>(cx: &LateContext<'a, 'tcx>, def_id: DefId) -> bool {
    cx.tcx.populate_implementations_for_trait_if_necessary(def_id);
    let trait_def = cx.tcx.lookup_trait_def(def_id);
    let mut impl_for_ref = false;
    trait_def.for_each_impl(cx.tcx, |impl_id| {
        let imp = cx.tcx.impl_trait_ref(impl_id).expect("trait impl is not found");
        impl_for_ref |= imp.self_ty().is_region_ptr();
    });
    impl_for_ref
}
