#![feature(macro_rules)]
#![feature(globs)]
#![feature(default_type_params)]
#![macro_escape]

use std::fmt;
use List::Nil;
use List::Cons;

#[deriving(Clone, PartialEq, Eq)]
pub enum List<A> {
    Nil,
    Cons(A, Box<List<A>>)
}

#[macro_export]
macro_rules! list[
    ()                       => (Nil);
    ($x:expr)                => (Cons($x, box Nil));
    ($x:expr, $($xs:expr),+) => (Cons($x, box list!($($xs),+)));
]

impl<A> List<A> {
    pub fn length(&self) -> int {
        self.fold_left(|a, _| a + 1, 0)
    }
}

impl<A: Clone> List<A> {
    pub fn hd(&self) -> Option<A> {
        match *self {
            Nil            => None,
            Cons(ref x, _) => Some(x.clone())
        }
    }

    pub fn tl(&self) -> Option<List<A>> {
        match *self {
            Nil                 => None,
            Cons(_, box ref xs) => Some(xs.clone())
        }
    }

    pub fn nth(&self, i: uint) -> Option<A> {
        match (i, self) {
            (_, &Nil)             => None,
            (0, &Cons(ref x, _))  => Some(x.clone()),
            (i, &Cons(_, ref xs)) => xs.nth(i - 1)
        }
    }

    pub fn rev(&self) -> List<A> {
        self.fold_left(|a, x| Cons(x.clone(), box a), Nil)
    }

    pub fn append(&self, ys: &List<A>) -> List<A> {
        self.clone().rev().rev_append(ys)
    }

    pub fn rev_append(&self, ys: &List<A>) -> List<A> {
        self.fold_left(|ys, x| Cons(x.clone(), box ys), ys.clone())
    }
}

pub fn concat<A: Clone>(xss: List<&List<A>>) -> List<A> {
    xss.fold_left(|xs, ys| xs.append(ys.clone()), list![])
}

pub fn flatten<A: Clone>(xss: List<&List<A>>) -> List<A> {
    concat(xss)
}

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
        assert_eq!(nil,             Nil);
        assert_eq!(list![1i],       Cons(1i, box Nil));
        assert_eq!(list![1i, 2],    Cons(1i, box Cons(2, box Nil)));
        assert_eq!(list![1i, 2, 3], Cons(1i, box Cons(2, box Cons(3, box Nil))));

        let nil: List<Box<int>> = list![];
        assert_eq!(nil,                         Nil);
        assert_eq!(list![box 1i],               Cons(box 1i, box Nil));
        assert_eq!(list![box 1i, box 2],        Cons(box 1i, box Cons(box 2, box Nil)));
        assert_eq!(list![box 1i, box 2, box 3], Cons(box 1i, box Cons(box 2, box Cons(box 3, box Nil))));
    }

    #[test]
    fn lenght_test() {
        let nil: List<int> = list![];
        assert_eq!(nil                  .length(), 0);
        assert_eq!(list![1i]            .length(), 1);
        assert_eq!(list![1i, 2]         .length(), 2);
        assert_eq!(list![1i, 2, 3]      .length(), 3);
        assert_eq!(list![1i, 2, 3, 4]   .length(), 4);
        assert_eq!(list![1i, 2, 3, 4, 5].length(), 5);
    }

    #[test]
    fn hd_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.hd(), None);
        assert_eq!(list![1i]      .hd(), Some(1i));
        assert_eq!(list![1i, 2]   .hd(), Some(1i));
        assert_eq!(list![1i, 2, 3].hd(), Some(1i));
    }

    #[test]
    fn tl_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.tl(), None);
        assert_eq!(list![1i]      .tl(), Some(list![]));
        assert_eq!(list![1i, 2]   .tl(), Some(list![2i]));
        assert_eq!(list![1i, 2, 3].tl(), Some(list![2i, 3]));
    }

    #[test]
    fn rev_test() {
        let nil: List<int> = list![];
        assert_eq!(nil                  .rev(), nil);
        assert_eq!(list![1i]            .rev(), list![1i]);
        assert_eq!(list![1i, 2]         .rev(), list![2i, 1]);
        assert_eq!(list![1i, 2, 3]      .rev(), list![3i, 2, 1]);
        assert_eq!(list![1i, 2, 3, 4]   .rev(), list![4i, 3, 2, 1]);
        assert_eq!(list![1i, 2, 3, 4, 5].rev(), list![5i, 4, 3, 2, 1]);
    }

    #[test]
    fn nth_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.nth(0),   None);
        assert_eq!(nil.nth(1),   None);
        assert_eq!(nil.nth(2),   None);
        assert_eq!(nil.nth(10),  None);
        assert_eq!(nil.nth(100), None);

        assert_eq!(list![1i].nth(0),   Some(1i));
        assert_eq!(list![1i].nth(1),   None);
        assert_eq!(list![1i].nth(2),   None);
        assert_eq!(list![1i].nth(10),  None);
        assert_eq!(list![1i].nth(100), None);

        assert_eq!(list![1i, 2].nth(0),   Some(1i));
        assert_eq!(list![1i, 2].nth(1),   Some(2i));
        assert_eq!(list![1i, 2].nth(2),   None);
        assert_eq!(list![1i, 2].nth(10),  None);
        assert_eq!(list![1i, 2].nth(100), None);

        assert_eq!(list![1i, 2, 3, 4, 5].nth(0),   Some(1i));
        assert_eq!(list![1i, 2, 3, 4, 5].nth(1),   Some(2i));
        assert_eq!(list![1i, 2, 3, 4, 5].nth(2),   Some(3i));
        assert_eq!(list![1i, 2, 3, 4, 5].nth(3),   Some(4i));
        assert_eq!(list![1i, 2, 3, 4, 5].nth(4),   Some(5i));
        assert_eq!(list![1i, 2, 3, 4, 5].nth(10),  None);
        assert_eq!(list![1i, 2, 3, 4, 5].nth(100), None);
    }

    #[test]
    fn append_test() {
        let nil: List<int> = list![];
        assert_eq!(nil               .append(&nil),                nil);
        assert_eq!(nil               .append(&list![1i]),          list![1i]);
        assert_eq!(list![1i]         .append(&nil),                list![1i]);
        assert_eq!(list![1i]         .append(&list![2i]),          list![1i, 2]);
        assert_eq!(list![1i, 2]      .append(&list![3]),           list![1i, 2, 3]);
        assert_eq!(list![1i]         .append(&list![2i, 3]),       list![1i, 2, 3]);
        assert_eq!(list![1i, 2, 3, 4].append(&list![5i, 6, 7, 8]), list![1i, 2, 3, 4, 5, 6, 7, 8]);
    }

    #[test]
    fn rev_append_test() {
        let nil: List<int> = list![];
        assert_eq!(nil               .rev_append(&nil),                nil);
        assert_eq!(nil               .rev_append(&list![1i]),          list![1i]);
        assert_eq!(list![1i]         .rev_append(&nil),                list![1i]);
        assert_eq!(list![1i]         .rev_append(&list![2i]),          list![1i, 2]);
        assert_eq!(list![1i, 2]      .rev_append(&list![3]),           list![2i, 1, 3]);
        assert_eq!(list![1i]         .rev_append(&list![2i, 3]),       list![1i, 2, 3]);
        assert_eq!(list![1i, 2, 3, 4].rev_append(&list![5i, 6, 7, 8]), list![4i, 3, 2, 1, 5, 6, 7, 8]);
    }

    #[test]
    fn concat_test() {
        let nil: List<&List<int>> = list![];
        let ws:  List<int> = list![];
        let xs:  List<int> = list![1i];
        let ys:  List<int> = list![2i, 3];
        let zs:  List<int> = list![4i, 5, 6];

        assert_eq!(concat(nil),                       list![]);
        assert_eq!(concat(list![&ws]),                list![]);
        assert_eq!(concat(list![&xs]),                list![1i]);
        assert_eq!(concat(list![&ys]),                list![2i, 3]);
        assert_eq!(concat(list![&zs]),                list![4i, 5, 6]);
        assert_eq!(concat(list![&ws, &xs]),           list![1i]);
        assert_eq!(concat(list![&ws, &xs, &ys]),      list![1i, 2, 3]);
        assert_eq!(concat(list![&ws, &xs, &ys, &zs]), list![1i, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn flatten_test() {
        let nil: List<&List<int>> = list![];
        let ws:  List<int> = list![];
        let xs:  List<int> = list![1i];
        let ys:  List<int> = list![2i, 3];
        let zs:  List<int> = list![4i, 5, 6];

        assert_eq!(flatten(nil),                       list![]);
        assert_eq!(flatten(list![&ws]),                list![]);
        assert_eq!(flatten(list![&xs]),                list![1i]);
        assert_eq!(flatten(list![&ys]),                list![2i, 3]);
        assert_eq!(flatten(list![&zs]),                list![4i, 5, 6]);
        assert_eq!(flatten(list![&ws, &xs]),           list![1i]);
        assert_eq!(flatten(list![&ws, &xs, &ys]),      list![1i, 2, 3]);
        assert_eq!(flatten(list![&ws, &xs, &ys, &zs]), list![1i, 2, 3, 4, 5, 6]);
    }
}
