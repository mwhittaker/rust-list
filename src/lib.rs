#![feature(macro_rules)]
#![feature(globs)]
#![feature(default_type_params)]
#![macro_escape]

//! [OCaml's List module](http://caml.inria.fr/pub/docs/manual-ocaml/libref/List.html) in rust!

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
        self.clone().into_hd()
    }

    pub fn tl(&self) -> Option<List<A>> {
        self.clone().into_tl()
    }

    pub fn nth(&self, i: uint) -> Option<A> {
        self.clone().into_nth(i)
    }

    pub fn rev(&self) -> List<A> {
        self.clone().reved()
    }

    pub fn append(&self, ys: &List<A>) -> List<A> {
        self.clone().appended(ys.clone())
    }

    pub fn rev_append(&self, ys: &List<A>) -> List<A> {
        self.clone().rev_appended(ys.clone())
    }

    pub fn concat<A: Clone>(xss: List<&List<A>>) -> List<A> {
        List::<A>::concated(xss.mapped(|l| l.clone()))
    }

    pub fn flatten<A: Clone>(xss: List<&List<A>>) -> List<A> {
        List::<A>::concat(xss)
    }
}

impl<A> List<A> {
    pub fn iter(&self, f: |&A| -> ()) {
        self.map(f);
    }

    pub fn map<B>(&self, f: |&A| -> B) -> List<B> {
        self.fold_left(|l, x| Cons(f(x), box l), list![]).reved()
    }

    pub fn rev_map<B>(&self, f: |&A| -> B) -> List<B> {
        self.map(f).reved()
    }

    pub fn fold_left<B>(&self, f: |B, &A| -> B, a: B) -> B {
        match *self {
            Nil => a,
            Cons(ref x, ref xs) => {
                let a = f(a, x);
                xs.fold_left(f, a)
            }
        }
    }

    pub fn fold_right<B>(&self, a: B, f: |&A, B| -> B) -> B {
        match *self {
            Nil => a,
            Cons(ref x, ref xs) => {
                let a = xs.fold_right(a, |x, a| f(x, a));
                f(x, a)
            }
        }
    }
}

impl<A> List<A> {
    pub fn into_hd(self) -> Option<A> {
        match self {
            Nil        => None,
            Cons(x, _) => Some(x)
        }
    }

    pub fn into_tl(self) -> Option<List<A>> {
        match self {
            Nil             => None,
            Cons(_, box xs) => Some(xs)
        }
    }

    pub fn into_nth(self, i: uint) -> Option<A> {
        match (i, self) {
            (_, Nil)             => None,
            (0, Cons(x, _))      => Some(x),
            (i, Cons(_, box xs)) => xs.into_nth(i - 1)
        }
    }

    fn reved(self) -> List<A> {
        self.folded_left(|a, x| Cons(x, box a), Nil)
    }

    pub fn appended(self, ys: List<A>) -> List<A> {
        self.reved().rev_appended(ys)
    }

    pub fn rev_appended(self, ys: List<A>) -> List<A> {
        self.folded_left(|ys, x| Cons(x, box ys), ys)
    }

    pub fn concated<A>(xss: List<List<A>>) -> List<A> {
        xss.folded_left(|xs, ys| xs.appended(ys), list![])
    }

    pub fn flattened<A>(xss: List<List<A>>) -> List<A> {
        List::<A>::concated(xss)
    }

    pub fn itered(self, f: |A| -> ()) {
        self.mapped(f);
    }

    pub fn mapped<B>(self, f: |A| -> B) -> List<B> {
        self.folded_left(|l, x| Cons(f(x), box l), list![]).reved()
    }

    pub fn rev_mapped<B>(self, f: |A| -> B) -> List<B> {
        self.mapped(f).reved()
    }

    pub fn folded_left<B>(self, f: |B, A| -> B, a: B) -> B {
        match self {
            Nil => a,
            Cons(x, xs) => {
                let a = f(a, x);
                xs.folded_left(f, a)
            }
        }
    }

    pub fn folded_right<B>(self, a: B, f: |A, B| -> B) -> B {
        match self {
            Nil => a,
            Cons(x, xs) => {
                let a = xs.folded_right(a, |x, a| f(x, a));
                f(x, a)
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
    fn into_hd_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.into_hd(), None);
        assert_eq!(list![1i]      .into_hd(), Some(1i));
        assert_eq!(list![1i, 2]   .into_hd(), Some(1i));
        assert_eq!(list![1i, 2, 3].into_hd(), Some(1i));
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
    fn into_tl_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.into_tl(), None);
        assert_eq!(list![1i]      .into_tl(), Some(list![]));
        assert_eq!(list![1i, 2]   .into_tl(), Some(list![2i]));
        assert_eq!(list![1i, 2, 3].into_tl(), Some(list![2i, 3]));
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
    fn reved_test() {
        let nil1: List<int> = list![];
        let nil2: List<int> = list![];
        assert_eq!(nil1                 .reved(), nil2);
        assert_eq!(list![1i]            .reved(), list![1i]);
        assert_eq!(list![1i, 2]         .reved(), list![2i, 1]);
        assert_eq!(list![1i, 2, 3]      .reved(), list![3i, 2, 1]);
        assert_eq!(list![1i, 2, 3, 4]   .reved(), list![4i, 3, 2, 1]);
        assert_eq!(list![1i, 2, 3, 4, 5].reved(), list![5i, 4, 3, 2, 1]);
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
    fn into_nth_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.into_nth(0),   None);
        let nil: List<int> = list![];
        assert_eq!(nil.into_nth(1),   None);
        let nil: List<int> = list![];
        assert_eq!(nil.into_nth(2),   None);
        let nil: List<int> = list![];
        assert_eq!(nil.into_nth(10),  None);
        let nil: List<int> = list![];
        assert_eq!(nil.into_nth(100), None);

        assert_eq!(list![1i].into_nth(0),   Some(1i));
        assert_eq!(list![1i].into_nth(1),   None);
        assert_eq!(list![1i].into_nth(2),   None);
        assert_eq!(list![1i].into_nth(10),  None);
        assert_eq!(list![1i].into_nth(100), None);

        assert_eq!(list![1i, 2].into_nth(0),   Some(1i));
        assert_eq!(list![1i, 2].into_nth(1),   Some(2i));
        assert_eq!(list![1i, 2].into_nth(2),   None);
        assert_eq!(list![1i, 2].into_nth(10),  None);
        assert_eq!(list![1i, 2].into_nth(100), None);

        assert_eq!(list![1i, 2, 3, 4, 5].into_nth(0),   Some(1i));
        assert_eq!(list![1i, 2, 3, 4, 5].into_nth(1),   Some(2i));
        assert_eq!(list![1i, 2, 3, 4, 5].into_nth(2),   Some(3i));
        assert_eq!(list![1i, 2, 3, 4, 5].into_nth(3),   Some(4i));
        assert_eq!(list![1i, 2, 3, 4, 5].into_nth(4),   Some(5i));
        assert_eq!(list![1i, 2, 3, 4, 5].into_nth(10),  None);
        assert_eq!(list![1i, 2, 3, 4, 5].into_nth(100), None);
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
    fn appended_test() {
        let nil1: List<int> = list![];
        let nil2: List<int> = list![];
        let nil3: List<int> = list![];
        assert_eq!(nil1              .appended(nil2),               nil3);

        let nil1: List<int> = list![];
        assert_eq!(nil1              .appended(list![1i]),          list![1i]);

        let nil1: List<int> = list![];
        assert_eq!(list![1i]         .appended(nil1),              list![1i]);
        assert_eq!(list![1i]         .appended(list![2i]),          list![1i, 2]);
        assert_eq!(list![1i, 2]      .appended(list![3]),           list![1i, 2, 3]);
        assert_eq!(list![1i]         .appended(list![2i, 3]),       list![1i, 2, 3]);
        assert_eq!(list![1i, 2, 3, 4].appended(list![5i, 6, 7, 8]), list![1i, 2, 3, 4, 5, 6, 7, 8]);
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
    fn rev_appended_test() {
        let nil1: List<int> = list![];
        let nil2: List<int> = list![];
        let nil3: List<int> = list![];
        assert_eq!(nil1              .rev_appended(nil2),               nil3);

        let nil1: List<int> = list![];
        assert_eq!(nil1              .rev_appended(list![1i]),          list![1i]);

        let nil1: List<int> = list![];
        assert_eq!(list![1i]         .rev_appended(nil1),               list![1i]);

        assert_eq!(list![1i]         .rev_appended(list![2i]),          list![1i, 2]);
        assert_eq!(list![1i, 2]      .rev_appended(list![3]),           list![2i, 1, 3]);
        assert_eq!(list![1i]         .rev_appended(list![2i, 3]),       list![1i, 2, 3]);
        assert_eq!(list![1i, 2, 3, 4].rev_appended(list![5i, 6, 7, 8]), list![4i, 3, 2, 1, 5, 6, 7, 8]);
    }


    #[test]
    fn concat_test() {
        let nil: List<&List<int>> = list![];
        let ws:  List<int> = list![];
        let xs:  List<int> = list![1i];
        let ys:  List<int> = list![2i, 3];
        let zs:  List<int> = list![4i, 5, 6];

        assert_eq!(List::<int>::concat(nil),                       list![]);
        assert_eq!(List::<int>::concat(list![&ws]),                list![]);
        assert_eq!(List::<int>::concat(list![&xs]),                list![1i]);
        assert_eq!(List::<int>::concat(list![&ys]),                list![2i, 3]);
        assert_eq!(List::<int>::concat(list![&zs]),                list![4i, 5, 6]);
        assert_eq!(List::<int>::concat(list![&ws, &xs]),           list![1i]);
        assert_eq!(List::<int>::concat(list![&ws, &xs, &ys]),      list![1i, 2, 3]);
        assert_eq!(List::<int>::concat(list![&ws, &xs, &ys, &zs]), list![1i, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn concated_test() {
        let nil: List<List<int>> = list![];
        let ws:  List<int> = list![];
        let xs:  List<int> = list![1i];
        let ys:  List<int> = list![2i, 3];
        let zs:  List<int> = list![4i, 5, 6];

        assert_eq!(List::<int>::concated(nil.clone()),                                           list![]);
        assert_eq!(List::<int>::concated(list![ws.clone()]),                                     list![]);
        assert_eq!(List::<int>::concated(list![xs.clone()]),                                     list![1i]);
        assert_eq!(List::<int>::concated(list![ys.clone()]),                                     list![2i, 3]);
        assert_eq!(List::<int>::concated(list![zs.clone()]),                                     list![4i, 5, 6]);
        assert_eq!(List::<int>::concated(list![ws.clone(), xs.clone()]),                         list![1i]);
        assert_eq!(List::<int>::concated(list![ws.clone(), xs.clone(), ys.clone()]),             list![1i, 2, 3]);
        assert_eq!(List::<int>::concated(list![ws.clone(), xs.clone(), ys.clone(), zs.clone()]), list![1i, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn flatten_test() {
        let nil: List<&List<int>> = list![];
        let ws:  List<int> = list![];
        let xs:  List<int> = list![1i];
        let ys:  List<int> = list![2i, 3];
        let zs:  List<int> = list![4i, 5, 6];

        assert_eq!(List::<int>::flatten(nil),                       list![]);
        assert_eq!(List::<int>::flatten(list![&ws]),                list![]);
        assert_eq!(List::<int>::flatten(list![&xs]),                list![1i]);
        assert_eq!(List::<int>::flatten(list![&ys]),                list![2i, 3]);
        assert_eq!(List::<int>::flatten(list![&zs]),                list![4i, 5, 6]);
        assert_eq!(List::<int>::flatten(list![&ws, &xs]),           list![1i]);
        assert_eq!(List::<int>::flatten(list![&ws, &xs, &ys]),      list![1i, 2, 3]);
        assert_eq!(List::<int>::flatten(list![&ws, &xs, &ys, &zs]), list![1i, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn flattened_test() {
        let nil: List<List<int>> = list![];
        let ws:  List<int> = list![];
        let xs:  List<int> = list![1i];
        let ys:  List<int> = list![2i, 3];
        let zs:  List<int> = list![4i, 5, 6];

        assert_eq!(List::<int>::flattened(nil.clone()),                                           list![]);
        assert_eq!(List::<int>::flattened(list![ws.clone()]),                                     list![]);
        assert_eq!(List::<int>::flattened(list![xs.clone()]),                                     list![1i]);
        assert_eq!(List::<int>::flattened(list![ys.clone()]),                                     list![2i, 3]);
        assert_eq!(List::<int>::flattened(list![zs.clone()]),                                     list![4i, 5, 6]);
        assert_eq!(List::<int>::flattened(list![ws.clone(), xs.clone()]),                         list![1i]);
        assert_eq!(List::<int>::flattened(list![ws.clone(), xs.clone(), ys.clone()]),             list![1i, 2, 3]);
        assert_eq!(List::<int>::flattened(list![ws.clone(), xs.clone(), ys.clone(), zs.clone()]), list![1i, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn iter_test() {
        let mut x = 0i;
        (list![1i, 2, 3, 4]).iter(|y| x += *y);
        assert_eq!(x, 10);

        let mut s = String::from_str("");
        (list!["a", "b", "c"]).iter(|y| s = s.clone() + *y);
        assert_eq!(s, String::from_str("abc"));
    }

    #[test]
    fn map_test() {
        let nil: List<int> = list![];
        assert_eq!(nil            .map(|x| *x),     list![]);
        assert_eq!(list![1i]      .map(|x| *x),     list![1i]);
        assert_eq!(list![1i, 2]   .map(|x| *x),     list![1i, 2]);
        assert_eq!(list![1i, 2, 3].map(|x| *x),     list![1i, 2, 3]);
        assert_eq!(list![1i]      .map(|x| *x + 1), list![2i]);
        assert_eq!(list![1i, 2]   .map(|x| *x + 1), list![2i, 3]);
        assert_eq!(list![1i, 2, 3].map(|x| *x + 1), list![2i, 3, 4]);
    }

    #[test]
    fn rev_map_test() {
        let nil: List<int> = list![];
        assert_eq!(nil            .rev_map(|x| *x),     list![]);
        assert_eq!(list![1i]      .rev_map(|x| *x),     list![1i]);
        assert_eq!(list![1i, 2]   .rev_map(|x| *x),     list![2i, 1]);
        assert_eq!(list![1i, 2, 3].rev_map(|x| *x),     list![3i, 2, 1]);
        assert_eq!(list![1i]      .rev_map(|x| *x + 1), list![2i]);
        assert_eq!(list![1i, 2]   .rev_map(|x| *x + 1), list![3i, 2]);
        assert_eq!(list![1i, 2, 3].rev_map(|x| *x + 1), list![4i, 3, 2]);
    }

    #[test]
    fn fold_left_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.fold_left(|a, x| a + *x, 0),  0);
        assert_eq!(nil.fold_left(|a, x| a + *x, 42), 42);
        assert_eq!(list![1i, 2, 3, 4].fold_left(|a, x| a + *x, 0), 10);
        assert_eq!(list![1i, 2, 3, 4].fold_left(|a, x| a * *x, 1), 24);
        assert_eq!(list!["a", "b", "c"].fold_left(|a, x| a + *x, String::from_str("")), String::from_str("abc"));
    }

    #[test]
    fn folded_left_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.folded_left(|a, x| a + x, 0),  0);
        let nil: List<int> = list![];
        assert_eq!(nil.folded_left(|a, x| a + x, 42), 42);
        assert_eq!(list![1i, 2, 3, 4].folded_left(|a, x| a + x, 0), 10);
        assert_eq!(list![1i, 2, 3, 4].folded_left(|a, x| a * x, 1), 24);
        assert_eq!(list!["a", "b", "c"].folded_left(|a, x| a + x, String::from_str("")), String::from_str("abc"));
    }

    #[test]
    fn fold_right_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.fold_right(0,  |x, a| a + *x),  0);
        assert_eq!(nil.fold_right(42, |x, a| a + *x),  42);
        assert_eq!(list![1i, 2, 3, 4].fold_right(0, |x, a| a + *x), 10);
        assert_eq!(list![1i, 2, 3, 4].fold_right(1, |x, a| a * *x), 24);
        assert_eq!(list!["a", "b", "c"].fold_right(String::from_str(""), |x, a| a + *x), String::from_str("cba"));
    }

    #[test]
    fn folded_right_test() {
        let nil: List<int> = list![];
        assert_eq!(nil.folded_right(0,  |x, a| a + x),  0);
        let nil: List<int> = list![];
        assert_eq!(nil.folded_right(42, |x, a| a + x),  42);
        assert_eq!(list![1i, 2, 3, 4].folded_right(0, |x, a| a + x), 10);
        assert_eq!(list![1i, 2, 3, 4].folded_right(1, |x, a| a * x), 24);
        assert_eq!(list!["a", "b", "c"].folded_right(String::from_str(""), |x, a| a + x), String::from_str("cba"));
    }
}
