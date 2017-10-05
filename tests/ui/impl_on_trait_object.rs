#![allow(unused)]

trait Foo {
    fn bar(&self) {}
}

impl Foo {
    fn bar(&self) {}
}

trait Bar<T> {
    fn foo(&self) {}
}

impl<T> Bar<T> + Sync {
    fn foo(&self) {}
}

trait FooExtensions {
    fn bar(&self);
}

impl<'a> FooExtensions for Foo + Sync + 'a {
    fn bar(&self) {}
}

fn main() {}
