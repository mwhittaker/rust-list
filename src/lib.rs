#![feature(macro_rules)]
#![feature(globs)]
#![feature(default_type_params)]

use std::fmt;
use List::Nil;
use List::Cons;

#[deriving(PartialEq, Eq)]
pub enum List<A> {
    Nil,
    Cons(A, Box<List<A>>)
}

macro_rules! list[
    ()                       => (Nil);
    ($x:expr)                => (Cons($x, box Nil));
    ($x:expr, $($xs:expr),+) => (Cons($x, box list!($($xs),+)));
]

impl<A> List<A> {
    pub fn map<B>(&self, f: |&A| -> B) -> List<B> {
        match *self {
            Nil                 => Nil,
            Cons(ref x, ref xs) => Cons (f(x), box xs.map(f))
        }
    }

    pub fn fold_left<B>(&self, f: |B, &A| -> B, a: B) -> B {
        match *self {
            Nil                 => a,
            Cons(ref x, ref xs) => {
                let a = f(a, x);
                xs.fold_left(f, a)
            }
        }
    }

    pub fn length(&self) -> int {
        self.fold_left(|a, _| a + 1, 0)
    }

}

impl<A: Clone> List<A> {
    pub fn rev(&self) -> List<A> {
        self.fold_left(|a, x| Cons(x.clone(), box a), Nil)
    }
}

impl<A: fmt::Show> List<A> {
    fn to_string(&self) -> String {
        fn help<A: fmt::Show>(l: &List<A>) -> String {
            match *l {
                Nil                      => String::from_str(""),
                Cons (ref x, box Nil)    => format!("{}", *x),
                Cons (ref x, box ref xs) => format!("{}, {}", *x, help(xs))
            }
        }
        format!("[{}]", help(self))
    }
}

impl<A: fmt::Show> fmt::Show for List<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::List::*;

    #[test]
    fn macro_test() {
        let nil: List<int> = list![];
        assert!(nil == Nil);

        assert!(list![1i] == Cons(1i, box Nil));
        assert!(list![1i, 2] == Cons(1i, box Cons(2, box Nil)));
    }
}
