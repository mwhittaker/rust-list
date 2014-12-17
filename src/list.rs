use std::fmt;
use self::List::Nil;
use self::List::Cons;

#[deriving(Clone, PartialEq, Eq)]
pub enum List<A> {
    Nil,
    Cons(A, Box<List<A>>)
}

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

    //pub fn nth(&self, i: int) -> Option<A> {
    //    panic!("TODO")
    //}

    pub fn rev(&self) -> List<A> {
        self.fold_left(|a, x| Cons(x.clone(), box a), Nil)
    }
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
        let nil: List<int> = lst![];
        assert_eq!(nil,             Nil);
        assert_eq!(lst![1i],       Cons(1i, box Nil));
        assert_eq!(lst![1i, 2],    Cons(1i, box Cons(2, box Nil)));
        assert_eq!(lst![1i, 2, 3], Cons(1i, box Cons(2, box Cons(3, box Nil))));

        let nil: List<Box<int>> = lst![];
        assert_eq!(nil,                         Nil);
        assert_eq!(lst![box 1i],               Cons(box 1i, box Nil));
        assert_eq!(lst![box 1i, box 2],        Cons(box 1i, box Cons(box 2, box Nil)));
        assert_eq!(lst![box 1i, box 2, box 3], Cons(box 1i, box Cons(box 2, box Cons(box 3, box Nil))));
    }

    #[test]
    fn lenght_test() {
        let nil: List<int> = lst![];
        assert_eq!(nil                  .length(), 0);
        assert_eq!(lst![1i]            .length(), 1);
        assert_eq!(lst![1i, 2]         .length(), 2);
        assert_eq!(lst![1i, 2, 3]      .length(), 3);
        assert_eq!(lst![1i, 2, 3, 4]   .length(), 4);
        assert_eq!(lst![1i, 2, 3, 4, 5].length(), 5);
    }

    #[test]
    fn hd_test() {
        let nil: List<int> = lst![];
        assert_eq!(nil.hd(), None);
        assert_eq!(lst![1i]      .hd(), Some(1i));
        assert_eq!(lst![1i, 2]   .hd(), Some(1i));
        assert_eq!(lst![1i, 2, 3].hd(), Some(1i));
    }

    #[test]
    fn tl_test() {
        let nil: List<int> = lst![];
        assert_eq!(nil.tl(), None);
        assert_eq!(lst![1i]      .tl(), Some(lst![]));
        assert_eq!(lst![1i, 2]   .tl(), Some(lst![2i]));
        assert_eq!(lst![1i, 2, 3].tl(), Some(lst![2i, 3]));
    }

    #[test]
    fn rev_test() {
        let nil: List<int> = lst![];
        assert_eq!(nil                 .rev(), nil);
        assert_eq!(lst![1i]            .rev(), lst![1i]);
        assert_eq!(lst![1i, 2]         .rev(), lst![2i, 1]);
        assert_eq!(lst![1i, 2, 3]      .rev(), lst![3i, 2, 1]);
        assert_eq!(lst![1i, 2, 3, 4]   .rev(), lst![4i, 3, 2, 1]);
        assert_eq!(lst![1i, 2, 3, 4, 5].rev(), lst![5i, 4, 3, 2, 1]);
    }
}
