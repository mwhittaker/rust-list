#[macro_export]
macro_rules! lst[
    ()                       => (Nil);
    ($x:expr)                => (Cons($x, box Nil));
    ($x:expr, $($xs:expr),+) => (Cons($x, box lst!($($xs),+)));
]
