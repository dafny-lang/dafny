#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
#![cfg_attr(any(), rustfmt::skip)]

pub mod _System {
    pub use crate::DafnyInt;
    pub use crate::DafnyType;
    pub use ::std::fmt::Debug;
    pub use ::std::fmt::Formatter;
    pub use ::std::fmt::Result;
    pub use crate::DafnyPrint;
    #[cfg(feature = "sync")] pub use ::std::sync::{Arc as Rc}; #[cfg(not(feature = "sync"))] pub use ::std::rc::Rc;
    pub use ::std::cmp::Eq;
    pub use ::std::hash::Hash;
    pub use ::std::cmp::PartialEq;
    pub use ::std::hash::Hasher;
    pub use ::std::convert::AsRef;
    pub use crate::SequenceIter;
    pub use crate::seq;

    pub type nat = DafnyInt;

    #[derive(Clone)]
    pub enum Tuple2<T0: DafnyType, T1: DafnyType> {
        _T2 {
            _0: T0,
            _1: T1
        }
    }

    impl<T0: DafnyType, T1: DafnyType> Tuple2<T0, T1> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple2::_T2{_0, _1, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple2::_T2{_0, _1, } => _1,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType> Debug
        for Tuple2<T0, T1> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType> DafnyPrint
        for Tuple2<T0, T1> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple2::_T2{_0, _1, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType> Tuple2<T0, T1> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple2<T0, T1>) -> Tuple2<__T0, __T1>> {
            Rc::new(move |this: Self| -> Tuple2<__T0, __T1>{
                    match this {
                        Tuple2::_T2{_0, _1, } => {
                            Tuple2::_T2 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash> PartialEq
        for Tuple2<T0, T1> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple2::_T2{_0, _1, }, Tuple2::_T2{_0: _2__0, _1: _2__1, }) => {
                    _0 == _2__0 && _1 == _2__1
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash> Eq
        for Tuple2<T0, T1> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash> Hash
        for Tuple2<T0, T1> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple2::_T2{_0, _1, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType> AsRef<Tuple2<T0, T1>>
        for Tuple2<T0, T1> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple0 {
        _T0 {}
    }

    impl Tuple0 {}

    impl Debug
        for Tuple0 {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl DafnyPrint
        for Tuple0 {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple0::_T0{} => {
                    write!(_formatter, "")?;
                    Ok(())
                },
            }
        }
    }

    impl Tuple0 {
        /// Enumerates all possible values of Tuple0
        pub fn _AllSingletonConstructors() -> SequenceIter<Rc<Tuple0>> {
            seq![Rc::new(Tuple0::_T0 {})].iter()
        }
    }

    impl PartialEq
        for Tuple0 {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple0::_T0{}, Tuple0::_T0{}) => {
                    true
                },
                _ => {
                    false
                },
            }
        }
    }

    impl Eq
        for Tuple0 {}

    impl Hash
        for Tuple0 {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple0::_T0{} => {
                    
                },
            }
        }
    }

    impl AsRef<Tuple0>
        for Tuple0 {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple1<T0: DafnyType> {
        _T1 {
            _0: T0
        }
    }

    impl<T0: DafnyType> Tuple1<T0> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple1::_T1{_0, } => _0,
            }
        }
    }

    impl<T0: DafnyType> Debug
        for Tuple1<T0> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType> DafnyPrint
        for Tuple1<T0> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple1::_T1{_0, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType> Tuple1<T0> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple1<T0>) -> Tuple1<__T0>> {
            Rc::new(move |this: Self| -> Tuple1<__T0>{
                    match this {
                        Tuple1::_T1{_0, } => {
                            Tuple1::_T1 {
                                _0: f_0.clone()(_0)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash> PartialEq
        for Tuple1<T0> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple1::_T1{_0, }, Tuple1::_T1{_0: _2__0, }) => {
                    _0 == _2__0
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash> Eq
        for Tuple1<T0> {}

    impl<T0: DafnyType + Hash> Hash
        for Tuple1<T0> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple1::_T1{_0, } => {
                    Hash::hash(_0, _state)
                },
            }
        }
    }

    impl<T0: DafnyType> AsRef<Tuple1<T0>>
        for Tuple1<T0> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple3<T0: DafnyType, T1: DafnyType, T2: DafnyType> {
        _T3 {
            _0: T0,
            _1: T1,
            _2: T2
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType> Tuple3<T0, T1, T2> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple3::_T3{_0, _1, _2, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple3::_T3{_0, _1, _2, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple3::_T3{_0, _1, _2, } => _2,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType> Debug
        for Tuple3<T0, T1, T2> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType> DafnyPrint
        for Tuple3<T0, T1, T2> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple3::_T3{_0, _1, _2, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType> Tuple3<T0, T1, T2> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple3<T0, T1, T2>) -> Tuple3<__T0, __T1, __T2>> {
            Rc::new(move |this: Self| -> Tuple3<__T0, __T1, __T2>{
                    match this {
                        Tuple3::_T3{_0, _1, _2, } => {
                            Tuple3::_T3 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash> PartialEq
        for Tuple3<T0, T1, T2> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple3::_T3{_0, _1, _2, }, Tuple3::_T3{_0: _2__0, _1: _2__1, _2: _2__2, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash> Eq
        for Tuple3<T0, T1, T2> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash> Hash
        for Tuple3<T0, T1, T2> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple3::_T3{_0, _1, _2, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType> AsRef<Tuple3<T0, T1, T2>>
        for Tuple3<T0, T1, T2> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple4<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType> {
        _T4 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType> Tuple4<T0, T1, T2, T3> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple4::_T4{_0, _1, _2, _3, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple4::_T4{_0, _1, _2, _3, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple4::_T4{_0, _1, _2, _3, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple4::_T4{_0, _1, _2, _3, } => _3,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType> Debug
        for Tuple4<T0, T1, T2, T3> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType> DafnyPrint
        for Tuple4<T0, T1, T2, T3> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple4::_T4{_0, _1, _2, _3, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType> Tuple4<T0, T1, T2, T3> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple4<T0, T1, T2, T3>) -> Tuple4<__T0, __T1, __T2, __T3>> {
            Rc::new(move |this: Self| -> Tuple4<__T0, __T1, __T2, __T3>{
                    match this {
                        Tuple4::_T4{_0, _1, _2, _3, } => {
                            Tuple4::_T4 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash> PartialEq
        for Tuple4<T0, T1, T2, T3> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple4::_T4{_0, _1, _2, _3, }, Tuple4::_T4{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash> Eq
        for Tuple4<T0, T1, T2, T3> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash> Hash
        for Tuple4<T0, T1, T2, T3> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple4::_T4{_0, _1, _2, _3, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType> AsRef<Tuple4<T0, T1, T2, T3>>
        for Tuple4<T0, T1, T2, T3> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple5<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType> {
        _T5 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType> Tuple5<T0, T1, T2, T3, T4> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple5::_T5{_0, _1, _2, _3, _4, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple5::_T5{_0, _1, _2, _3, _4, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple5::_T5{_0, _1, _2, _3, _4, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple5::_T5{_0, _1, _2, _3, _4, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple5::_T5{_0, _1, _2, _3, _4, } => _4,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType> Debug
        for Tuple5<T0, T1, T2, T3, T4> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType> DafnyPrint
        for Tuple5<T0, T1, T2, T3, T4> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple5::_T5{_0, _1, _2, _3, _4, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType> Tuple5<T0, T1, T2, T3, T4> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple5<T0, T1, T2, T3, T4>) -> Tuple5<__T0, __T1, __T2, __T3, __T4>> {
            Rc::new(move |this: Self| -> Tuple5<__T0, __T1, __T2, __T3, __T4>{
                    match this {
                        Tuple5::_T5{_0, _1, _2, _3, _4, } => {
                            Tuple5::_T5 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash> PartialEq
        for Tuple5<T0, T1, T2, T3, T4> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple5::_T5{_0, _1, _2, _3, _4, }, Tuple5::_T5{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash> Eq
        for Tuple5<T0, T1, T2, T3, T4> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash> Hash
        for Tuple5<T0, T1, T2, T3, T4> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple5::_T5{_0, _1, _2, _3, _4, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType> AsRef<Tuple5<T0, T1, T2, T3, T4>>
        for Tuple5<T0, T1, T2, T3, T4> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple6<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType> {
        _T6 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType> Tuple6<T0, T1, T2, T3, T4, T5> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _5,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType> Debug
        for Tuple6<T0, T1, T2, T3, T4, T5> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType> DafnyPrint
        for Tuple6<T0, T1, T2, T3, T4, T5> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType> Tuple6<T0, T1, T2, T3, T4, T5> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple6<T0, T1, T2, T3, T4, T5>) -> Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>> {
            Rc::new(move |this: Self| -> Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>{
                    match this {
                        Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => {
                            Tuple6::_T6 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash> PartialEq
        for Tuple6<T0, T1, T2, T3, T4, T5> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple6::_T6{_0, _1, _2, _3, _4, _5, }, Tuple6::_T6{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash> Eq
        for Tuple6<T0, T1, T2, T3, T4, T5> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash> Hash
        for Tuple6<T0, T1, T2, T3, T4, T5> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType> AsRef<Tuple6<T0, T1, T2, T3, T4, T5>>
        for Tuple6<T0, T1, T2, T3, T4, T5> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple7<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType> {
        _T7 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType> Tuple7<T0, T1, T2, T3, T4, T5, T6> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _6,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType> Debug
        for Tuple7<T0, T1, T2, T3, T4, T5, T6> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType> DafnyPrint
        for Tuple7<T0, T1, T2, T3, T4, T5, T6> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType> Tuple7<T0, T1, T2, T3, T4, T5, T6> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple7<T0, T1, T2, T3, T4, T5, T6>) -> Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>> {
            Rc::new(move |this: Self| -> Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>{
                    match this {
                        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => {
                            Tuple7::_T7 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash> PartialEq
        for Tuple7<T0, T1, T2, T3, T4, T5, T6> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, }, Tuple7::_T7{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash> Eq
        for Tuple7<T0, T1, T2, T3, T4, T5, T6> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash> Hash
        for Tuple7<T0, T1, T2, T3, T4, T5, T6> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType> AsRef<Tuple7<T0, T1, T2, T3, T4, T5, T6>>
        for Tuple7<T0, T1, T2, T3, T4, T5, T6> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple8<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType> {
        _T8 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType> Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _7,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType> Debug
        for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType> DafnyPrint
        for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType> Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>) -> Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>> {
            Rc::new(move |this: Self| -> Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>{
                    match this {
                        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => {
                            Tuple8::_T8 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash> PartialEq
        for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, }, Tuple8::_T8{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash> Eq
        for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash> Hash
        for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType> AsRef<Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>>
        for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple9<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType> {
        _T9 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType> Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _8,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType> Debug
        for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType> DafnyPrint
        for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType> Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>) -> Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>> {
            Rc::new(move |this: Self| -> Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>{
                    match this {
                        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => {
                            Tuple9::_T9 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash> PartialEq
        for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, }, Tuple9::_T9{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash> Eq
        for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash> Hash
        for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType> AsRef<Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>
        for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple10<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType> {
        _T10 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType> Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _9,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType> Debug
        for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType> DafnyPrint
        for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType> Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>) -> Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>> {
            Rc::new(move |this: Self| -> Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>{
                    match this {
                        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => {
                            Tuple10::_T10 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash> PartialEq
        for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, }, Tuple10::_T10{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash> Eq
        for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash> Hash
        for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType> AsRef<Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>
        for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple11<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType> {
        _T11 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType> Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _10,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType> Debug
        for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType> DafnyPrint
        for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType> Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>) -> Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>> {
            Rc::new(move |this: Self| -> Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>{
                    match this {
                        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => {
                            Tuple11::_T11 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash> PartialEq
        for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, }, Tuple11::_T11{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash> Eq
        for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash> Hash
        for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType> AsRef<Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>
        for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple12<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType> {
        _T12 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10,
            _11: T11
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType> Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _10,
            }
        }
        /// Returns a borrow of the field _11
        pub fn _11(&self) -> &T11 {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _11,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType> Debug
        for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType> DafnyPrint
        for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_11, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType> Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType, __T11: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>, f_11: Rc<impl ::std::ops::Fn(T11) -> __T11 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>) -> Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>> {
            Rc::new(move |this: Self| -> Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>{
                    match this {
                        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => {
                            Tuple12::_T12 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10),
                                _11: f_11.clone()(_11)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash> PartialEq
        for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, }, Tuple12::_T12{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, _11: _2__11, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10 && _11 == _2__11
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash> Eq
        for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash, T11: DafnyType + Hash> Hash
        for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state);
                    Hash::hash(_11, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType> AsRef<Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>
        for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple13<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType> {
        _T13 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10,
            _11: T11,
            _12: T12
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType> Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _10,
            }
        }
        /// Returns a borrow of the field _11
        pub fn _11(&self) -> &T11 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _11,
            }
        }
        /// Returns a borrow of the field _12
        pub fn _12(&self) -> &T12 {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _12,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType> Debug
        for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType> DafnyPrint
        for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_11, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_12, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType> Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType, __T11: DafnyType, __T12: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>, f_11: Rc<impl ::std::ops::Fn(T11) -> __T11 + 'static>, f_12: Rc<impl ::std::ops::Fn(T12) -> __T12 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>) -> Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>> {
            Rc::new(move |this: Self| -> Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>{
                    match this {
                        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => {
                            Tuple13::_T13 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10),
                                _11: f_11.clone()(_11),
                                _12: f_12.clone()(_12)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash> PartialEq
        for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, }, Tuple13::_T13{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, _11: _2__11, _12: _2__12, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10 && _11 == _2__11 && _12 == _2__12
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash> Eq
        for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash, T11: DafnyType + Hash, T12: DafnyType + Hash> Hash
        for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state);
                    Hash::hash(_11, _state);
                    Hash::hash(_12, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType> AsRef<Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>
        for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple14<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType> {
        _T14 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10,
            _11: T11,
            _12: T12,
            _13: T13
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType> Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _10,
            }
        }
        /// Returns a borrow of the field _11
        pub fn _11(&self) -> &T11 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _11,
            }
        }
        /// Returns a borrow of the field _12
        pub fn _12(&self) -> &T12 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _12,
            }
        }
        /// Returns a borrow of the field _13
        pub fn _13(&self) -> &T13 {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _13,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType> Debug
        for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType> DafnyPrint
        for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_11, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_12, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_13, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType> Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType, __T11: DafnyType, __T12: DafnyType, __T13: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>, f_11: Rc<impl ::std::ops::Fn(T11) -> __T11 + 'static>, f_12: Rc<impl ::std::ops::Fn(T12) -> __T12 + 'static>, f_13: Rc<impl ::std::ops::Fn(T13) -> __T13 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>) -> Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>> {
            Rc::new(move |this: Self| -> Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>{
                    match this {
                        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => {
                            Tuple14::_T14 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10),
                                _11: f_11.clone()(_11),
                                _12: f_12.clone()(_12),
                                _13: f_13.clone()(_13)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash> PartialEq
        for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, }, Tuple14::_T14{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, _11: _2__11, _12: _2__12, _13: _2__13, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10 && _11 == _2__11 && _12 == _2__12 && _13 == _2__13
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash> Eq
        for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash, T11: DafnyType + Hash, T12: DafnyType + Hash, T13: DafnyType + Hash> Hash
        for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state);
                    Hash::hash(_11, _state);
                    Hash::hash(_12, _state);
                    Hash::hash(_13, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType> AsRef<Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>
        for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple15<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType> {
        _T15 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10,
            _11: T11,
            _12: T12,
            _13: T13,
            _14: T14
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType> Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _10,
            }
        }
        /// Returns a borrow of the field _11
        pub fn _11(&self) -> &T11 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _11,
            }
        }
        /// Returns a borrow of the field _12
        pub fn _12(&self) -> &T12 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _12,
            }
        }
        /// Returns a borrow of the field _13
        pub fn _13(&self) -> &T13 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _13,
            }
        }
        /// Returns a borrow of the field _14
        pub fn _14(&self) -> &T14 {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _14,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType> Debug
        for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType> DafnyPrint
        for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_11, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_12, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_13, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_14, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType> Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType, __T11: DafnyType, __T12: DafnyType, __T13: DafnyType, __T14: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>, f_11: Rc<impl ::std::ops::Fn(T11) -> __T11 + 'static>, f_12: Rc<impl ::std::ops::Fn(T12) -> __T12 + 'static>, f_13: Rc<impl ::std::ops::Fn(T13) -> __T13 + 'static>, f_14: Rc<impl ::std::ops::Fn(T14) -> __T14 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>) -> Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>> {
            Rc::new(move |this: Self| -> Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>{
                    match this {
                        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => {
                            Tuple15::_T15 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10),
                                _11: f_11.clone()(_11),
                                _12: f_12.clone()(_12),
                                _13: f_13.clone()(_13),
                                _14: f_14.clone()(_14)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash> PartialEq
        for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, }, Tuple15::_T15{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, _11: _2__11, _12: _2__12, _13: _2__13, _14: _2__14, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10 && _11 == _2__11 && _12 == _2__12 && _13 == _2__13 && _14 == _2__14
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash> Eq
        for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash, T11: DafnyType + Hash, T12: DafnyType + Hash, T13: DafnyType + Hash, T14: DafnyType + Hash> Hash
        for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state);
                    Hash::hash(_11, _state);
                    Hash::hash(_12, _state);
                    Hash::hash(_13, _state);
                    Hash::hash(_14, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType> AsRef<Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>
        for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple16<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType> {
        _T16 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10,
            _11: T11,
            _12: T12,
            _13: T13,
            _14: T14,
            _15: T15
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType> Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _10,
            }
        }
        /// Returns a borrow of the field _11
        pub fn _11(&self) -> &T11 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _11,
            }
        }
        /// Returns a borrow of the field _12
        pub fn _12(&self) -> &T12 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _12,
            }
        }
        /// Returns a borrow of the field _13
        pub fn _13(&self) -> &T13 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _13,
            }
        }
        /// Returns a borrow of the field _14
        pub fn _14(&self) -> &T14 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _14,
            }
        }
        /// Returns a borrow of the field _15
        pub fn _15(&self) -> &T15 {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _15,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType> Debug
        for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType> DafnyPrint
        for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_11, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_12, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_13, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_14, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_15, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType> Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType, __T11: DafnyType, __T12: DafnyType, __T13: DafnyType, __T14: DafnyType, __T15: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>, f_11: Rc<impl ::std::ops::Fn(T11) -> __T11 + 'static>, f_12: Rc<impl ::std::ops::Fn(T12) -> __T12 + 'static>, f_13: Rc<impl ::std::ops::Fn(T13) -> __T13 + 'static>, f_14: Rc<impl ::std::ops::Fn(T14) -> __T14 + 'static>, f_15: Rc<impl ::std::ops::Fn(T15) -> __T15 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>) -> Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>> {
            Rc::new(move |this: Self| -> Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>{
                    match this {
                        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => {
                            Tuple16::_T16 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10),
                                _11: f_11.clone()(_11),
                                _12: f_12.clone()(_12),
                                _13: f_13.clone()(_13),
                                _14: f_14.clone()(_14),
                                _15: f_15.clone()(_15)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash> PartialEq
        for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, }, Tuple16::_T16{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, _11: _2__11, _12: _2__12, _13: _2__13, _14: _2__14, _15: _2__15, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10 && _11 == _2__11 && _12 == _2__12 && _13 == _2__13 && _14 == _2__14 && _15 == _2__15
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash> Eq
        for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash, T11: DafnyType + Hash, T12: DafnyType + Hash, T13: DafnyType + Hash, T14: DafnyType + Hash, T15: DafnyType + Hash> Hash
        for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state);
                    Hash::hash(_11, _state);
                    Hash::hash(_12, _state);
                    Hash::hash(_13, _state);
                    Hash::hash(_14, _state);
                    Hash::hash(_15, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType> AsRef<Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>
        for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple17<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType> {
        _T17 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10,
            _11: T11,
            _12: T12,
            _13: T13,
            _14: T14,
            _15: T15,
            _16: T16
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType> Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _10,
            }
        }
        /// Returns a borrow of the field _11
        pub fn _11(&self) -> &T11 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _11,
            }
        }
        /// Returns a borrow of the field _12
        pub fn _12(&self) -> &T12 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _12,
            }
        }
        /// Returns a borrow of the field _13
        pub fn _13(&self) -> &T13 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _13,
            }
        }
        /// Returns a borrow of the field _14
        pub fn _14(&self) -> &T14 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _14,
            }
        }
        /// Returns a borrow of the field _15
        pub fn _15(&self) -> &T15 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _15,
            }
        }
        /// Returns a borrow of the field _16
        pub fn _16(&self) -> &T16 {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _16,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType> Debug
        for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType> DafnyPrint
        for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_11, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_12, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_13, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_14, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_15, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_16, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType> Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType, __T11: DafnyType, __T12: DafnyType, __T13: DafnyType, __T14: DafnyType, __T15: DafnyType, __T16: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>, f_11: Rc<impl ::std::ops::Fn(T11) -> __T11 + 'static>, f_12: Rc<impl ::std::ops::Fn(T12) -> __T12 + 'static>, f_13: Rc<impl ::std::ops::Fn(T13) -> __T13 + 'static>, f_14: Rc<impl ::std::ops::Fn(T14) -> __T14 + 'static>, f_15: Rc<impl ::std::ops::Fn(T15) -> __T15 + 'static>, f_16: Rc<impl ::std::ops::Fn(T16) -> __T16 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>) -> Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>> {
            Rc::new(move |this: Self| -> Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>{
                    match this {
                        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => {
                            Tuple17::_T17 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10),
                                _11: f_11.clone()(_11),
                                _12: f_12.clone()(_12),
                                _13: f_13.clone()(_13),
                                _14: f_14.clone()(_14),
                                _15: f_15.clone()(_15),
                                _16: f_16.clone()(_16)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash, T16: DafnyType + Eq + Hash> PartialEq
        for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, }, Tuple17::_T17{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, _11: _2__11, _12: _2__12, _13: _2__13, _14: _2__14, _15: _2__15, _16: _2__16, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10 && _11 == _2__11 && _12 == _2__12 && _13 == _2__13 && _14 == _2__14 && _15 == _2__15 && _16 == _2__16
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash, T16: DafnyType + Eq + Hash> Eq
        for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash, T11: DafnyType + Hash, T12: DafnyType + Hash, T13: DafnyType + Hash, T14: DafnyType + Hash, T15: DafnyType + Hash, T16: DafnyType + Hash> Hash
        for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state);
                    Hash::hash(_11, _state);
                    Hash::hash(_12, _state);
                    Hash::hash(_13, _state);
                    Hash::hash(_14, _state);
                    Hash::hash(_15, _state);
                    Hash::hash(_16, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType> AsRef<Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>
        for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple18<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType> {
        _T18 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10,
            _11: T11,
            _12: T12,
            _13: T13,
            _14: T14,
            _15: T15,
            _16: T16,
            _17: T17
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType> Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _10,
            }
        }
        /// Returns a borrow of the field _11
        pub fn _11(&self) -> &T11 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _11,
            }
        }
        /// Returns a borrow of the field _12
        pub fn _12(&self) -> &T12 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _12,
            }
        }
        /// Returns a borrow of the field _13
        pub fn _13(&self) -> &T13 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _13,
            }
        }
        /// Returns a borrow of the field _14
        pub fn _14(&self) -> &T14 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _14,
            }
        }
        /// Returns a borrow of the field _15
        pub fn _15(&self) -> &T15 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _15,
            }
        }
        /// Returns a borrow of the field _16
        pub fn _16(&self) -> &T16 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _16,
            }
        }
        /// Returns a borrow of the field _17
        pub fn _17(&self) -> &T17 {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _17,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType> Debug
        for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType> DafnyPrint
        for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_11, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_12, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_13, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_14, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_15, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_16, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_17, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType> Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType, __T11: DafnyType, __T12: DafnyType, __T13: DafnyType, __T14: DafnyType, __T15: DafnyType, __T16: DafnyType, __T17: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>, f_11: Rc<impl ::std::ops::Fn(T11) -> __T11 + 'static>, f_12: Rc<impl ::std::ops::Fn(T12) -> __T12 + 'static>, f_13: Rc<impl ::std::ops::Fn(T13) -> __T13 + 'static>, f_14: Rc<impl ::std::ops::Fn(T14) -> __T14 + 'static>, f_15: Rc<impl ::std::ops::Fn(T15) -> __T15 + 'static>, f_16: Rc<impl ::std::ops::Fn(T16) -> __T16 + 'static>, f_17: Rc<impl ::std::ops::Fn(T17) -> __T17 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>) -> Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>> {
            Rc::new(move |this: Self| -> Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>{
                    match this {
                        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => {
                            Tuple18::_T18 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10),
                                _11: f_11.clone()(_11),
                                _12: f_12.clone()(_12),
                                _13: f_13.clone()(_13),
                                _14: f_14.clone()(_14),
                                _15: f_15.clone()(_15),
                                _16: f_16.clone()(_16),
                                _17: f_17.clone()(_17)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash, T16: DafnyType + Eq + Hash, T17: DafnyType + Eq + Hash> PartialEq
        for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, }, Tuple18::_T18{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, _11: _2__11, _12: _2__12, _13: _2__13, _14: _2__14, _15: _2__15, _16: _2__16, _17: _2__17, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10 && _11 == _2__11 && _12 == _2__12 && _13 == _2__13 && _14 == _2__14 && _15 == _2__15 && _16 == _2__16 && _17 == _2__17
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash, T16: DafnyType + Eq + Hash, T17: DafnyType + Eq + Hash> Eq
        for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash, T11: DafnyType + Hash, T12: DafnyType + Hash, T13: DafnyType + Hash, T14: DafnyType + Hash, T15: DafnyType + Hash, T16: DafnyType + Hash, T17: DafnyType + Hash> Hash
        for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state);
                    Hash::hash(_11, _state);
                    Hash::hash(_12, _state);
                    Hash::hash(_13, _state);
                    Hash::hash(_14, _state);
                    Hash::hash(_15, _state);
                    Hash::hash(_16, _state);
                    Hash::hash(_17, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType> AsRef<Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>
        for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple19<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType> {
        _T19 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10,
            _11: T11,
            _12: T12,
            _13: T13,
            _14: T14,
            _15: T15,
            _16: T16,
            _17: T17,
            _18: T18
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType> Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _10,
            }
        }
        /// Returns a borrow of the field _11
        pub fn _11(&self) -> &T11 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _11,
            }
        }
        /// Returns a borrow of the field _12
        pub fn _12(&self) -> &T12 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _12,
            }
        }
        /// Returns a borrow of the field _13
        pub fn _13(&self) -> &T13 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _13,
            }
        }
        /// Returns a borrow of the field _14
        pub fn _14(&self) -> &T14 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _14,
            }
        }
        /// Returns a borrow of the field _15
        pub fn _15(&self) -> &T15 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _15,
            }
        }
        /// Returns a borrow of the field _16
        pub fn _16(&self) -> &T16 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _16,
            }
        }
        /// Returns a borrow of the field _17
        pub fn _17(&self) -> &T17 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _17,
            }
        }
        /// Returns a borrow of the field _18
        pub fn _18(&self) -> &T18 {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _18,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType> Debug
        for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType> DafnyPrint
        for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_11, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_12, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_13, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_14, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_15, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_16, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_17, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_18, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType> Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType, __T11: DafnyType, __T12: DafnyType, __T13: DafnyType, __T14: DafnyType, __T15: DafnyType, __T16: DafnyType, __T17: DafnyType, __T18: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>, f_11: Rc<impl ::std::ops::Fn(T11) -> __T11 + 'static>, f_12: Rc<impl ::std::ops::Fn(T12) -> __T12 + 'static>, f_13: Rc<impl ::std::ops::Fn(T13) -> __T13 + 'static>, f_14: Rc<impl ::std::ops::Fn(T14) -> __T14 + 'static>, f_15: Rc<impl ::std::ops::Fn(T15) -> __T15 + 'static>, f_16: Rc<impl ::std::ops::Fn(T16) -> __T16 + 'static>, f_17: Rc<impl ::std::ops::Fn(T17) -> __T17 + 'static>, f_18: Rc<impl ::std::ops::Fn(T18) -> __T18 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>) -> Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>> {
            Rc::new(move |this: Self| -> Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>{
                    match this {
                        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => {
                            Tuple19::_T19 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10),
                                _11: f_11.clone()(_11),
                                _12: f_12.clone()(_12),
                                _13: f_13.clone()(_13),
                                _14: f_14.clone()(_14),
                                _15: f_15.clone()(_15),
                                _16: f_16.clone()(_16),
                                _17: f_17.clone()(_17),
                                _18: f_18.clone()(_18)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash, T16: DafnyType + Eq + Hash, T17: DafnyType + Eq + Hash, T18: DafnyType + Eq + Hash> PartialEq
        for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, }, Tuple19::_T19{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, _11: _2__11, _12: _2__12, _13: _2__13, _14: _2__14, _15: _2__15, _16: _2__16, _17: _2__17, _18: _2__18, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10 && _11 == _2__11 && _12 == _2__12 && _13 == _2__13 && _14 == _2__14 && _15 == _2__15 && _16 == _2__16 && _17 == _2__17 && _18 == _2__18
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash, T16: DafnyType + Eq + Hash, T17: DafnyType + Eq + Hash, T18: DafnyType + Eq + Hash> Eq
        for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash, T11: DafnyType + Hash, T12: DafnyType + Hash, T13: DafnyType + Hash, T14: DafnyType + Hash, T15: DafnyType + Hash, T16: DafnyType + Hash, T17: DafnyType + Hash, T18: DafnyType + Hash> Hash
        for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state);
                    Hash::hash(_11, _state);
                    Hash::hash(_12, _state);
                    Hash::hash(_13, _state);
                    Hash::hash(_14, _state);
                    Hash::hash(_15, _state);
                    Hash::hash(_16, _state);
                    Hash::hash(_17, _state);
                    Hash::hash(_18, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType> AsRef<Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>
        for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
        fn as_ref(&self) -> &Self {
            self
        }
    }

    #[derive(Clone)]
    pub enum Tuple20<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType, T19: DafnyType> {
        _T20 {
            _0: T0,
            _1: T1,
            _2: T2,
            _3: T3,
            _4: T4,
            _5: T5,
            _6: T6,
            _7: T7,
            _8: T8,
            _9: T9,
            _10: T10,
            _11: T11,
            _12: T12,
            _13: T13,
            _14: T14,
            _15: T15,
            _16: T16,
            _17: T17,
            _18: T18,
            _19: T19
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType, T19: DafnyType> Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
        /// Returns a borrow of the field _0
        pub fn _0(&self) -> &T0 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _0,
            }
        }
        /// Returns a borrow of the field _1
        pub fn _1(&self) -> &T1 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _1,
            }
        }
        /// Returns a borrow of the field _2
        pub fn _2(&self) -> &T2 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _2,
            }
        }
        /// Returns a borrow of the field _3
        pub fn _3(&self) -> &T3 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _3,
            }
        }
        /// Returns a borrow of the field _4
        pub fn _4(&self) -> &T4 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _4,
            }
        }
        /// Returns a borrow of the field _5
        pub fn _5(&self) -> &T5 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _5,
            }
        }
        /// Returns a borrow of the field _6
        pub fn _6(&self) -> &T6 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _6,
            }
        }
        /// Returns a borrow of the field _7
        pub fn _7(&self) -> &T7 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _7,
            }
        }
        /// Returns a borrow of the field _8
        pub fn _8(&self) -> &T8 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _8,
            }
        }
        /// Returns a borrow of the field _9
        pub fn _9(&self) -> &T9 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _9,
            }
        }
        /// Returns a borrow of the field _10
        pub fn _10(&self) -> &T10 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _10,
            }
        }
        /// Returns a borrow of the field _11
        pub fn _11(&self) -> &T11 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _11,
            }
        }
        /// Returns a borrow of the field _12
        pub fn _12(&self) -> &T12 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _12,
            }
        }
        /// Returns a borrow of the field _13
        pub fn _13(&self) -> &T13 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _13,
            }
        }
        /// Returns a borrow of the field _14
        pub fn _14(&self) -> &T14 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _14,
            }
        }
        /// Returns a borrow of the field _15
        pub fn _15(&self) -> &T15 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _15,
            }
        }
        /// Returns a borrow of the field _16
        pub fn _16(&self) -> &T16 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _16,
            }
        }
        /// Returns a borrow of the field _17
        pub fn _17(&self) -> &T17 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _17,
            }
        }
        /// Returns a borrow of the field _18
        pub fn _18(&self) -> &T18 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _18,
            }
        }
        /// Returns a borrow of the field _19
        pub fn _19(&self) -> &T19 {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _19,
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType, T19: DafnyType> Debug
        for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType, T19: DafnyType> DafnyPrint
        for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => {
                    write!(_formatter, "(")?;
                    DafnyPrint::fmt_print(_0, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_1, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_2, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_3, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_4, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_5, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_6, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_7, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_8, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_9, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_10, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_11, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_12, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_13, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_14, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_15, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_16, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_17, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_18, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    DafnyPrint::fmt_print(_19, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType, T19: DafnyType> Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
        /// Given type parameter conversions, returns a lambda to convert this structure
        pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType, __T4: DafnyType, __T5: DafnyType, __T6: DafnyType, __T7: DafnyType, __T8: DafnyType, __T9: DafnyType, __T10: DafnyType, __T11: DafnyType, __T12: DafnyType, __T13: DafnyType, __T14: DafnyType, __T15: DafnyType, __T16: DafnyType, __T17: DafnyType, __T18: DafnyType, __T19: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T0) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(T1) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(T2) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(T3) -> __T3 + 'static>, f_4: Rc<impl ::std::ops::Fn(T4) -> __T4 + 'static>, f_5: Rc<impl ::std::ops::Fn(T5) -> __T5 + 'static>, f_6: Rc<impl ::std::ops::Fn(T6) -> __T6 + 'static>, f_7: Rc<impl ::std::ops::Fn(T7) -> __T7 + 'static>, f_8: Rc<impl ::std::ops::Fn(T8) -> __T8 + 'static>, f_9: Rc<impl ::std::ops::Fn(T9) -> __T9 + 'static>, f_10: Rc<impl ::std::ops::Fn(T10) -> __T10 + 'static>, f_11: Rc<impl ::std::ops::Fn(T11) -> __T11 + 'static>, f_12: Rc<impl ::std::ops::Fn(T12) -> __T12 + 'static>, f_13: Rc<impl ::std::ops::Fn(T13) -> __T13 + 'static>, f_14: Rc<impl ::std::ops::Fn(T14) -> __T14 + 'static>, f_15: Rc<impl ::std::ops::Fn(T15) -> __T15 + 'static>, f_16: Rc<impl ::std::ops::Fn(T16) -> __T16 + 'static>, f_17: Rc<impl ::std::ops::Fn(T17) -> __T17 + 'static>, f_18: Rc<impl ::std::ops::Fn(T18) -> __T18 + 'static>, f_19: Rc<impl ::std::ops::Fn(T19) -> __T19 + 'static>) -> Rc<impl ::std::ops::Fn(Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>) -> Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>> {
            Rc::new(move |this: Self| -> Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>{
                    match this {
                        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => {
                            Tuple20::_T20 {
                                _0: f_0.clone()(_0),
                                _1: f_1.clone()(_1),
                                _2: f_2.clone()(_2),
                                _3: f_3.clone()(_3),
                                _4: f_4.clone()(_4),
                                _5: f_5.clone()(_5),
                                _6: f_6.clone()(_6),
                                _7: f_7.clone()(_7),
                                _8: f_8.clone()(_8),
                                _9: f_9.clone()(_9),
                                _10: f_10.clone()(_10),
                                _11: f_11.clone()(_11),
                                _12: f_12.clone()(_12),
                                _13: f_13.clone()(_13),
                                _14: f_14.clone()(_14),
                                _15: f_15.clone()(_15),
                                _16: f_16.clone()(_16),
                                _17: f_17.clone()(_17),
                                _18: f_18.clone()(_18),
                                _19: f_19.clone()(_19)
                            }
                        },
                    }
                })
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash, T16: DafnyType + Eq + Hash, T17: DafnyType + Eq + Hash, T18: DafnyType + Eq + Hash, T19: DafnyType + Eq + Hash> PartialEq
        for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
        fn eq(&self, other: &Self) -> bool {
            match (
                    self,
                    other
                ) {
                (Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, }, Tuple20::_T20{_0: _2__0, _1: _2__1, _2: _2__2, _3: _2__3, _4: _2__4, _5: _2__5, _6: _2__6, _7: _2__7, _8: _2__8, _9: _2__9, _10: _2__10, _11: _2__11, _12: _2__12, _13: _2__13, _14: _2__14, _15: _2__15, _16: _2__16, _17: _2__17, _18: _2__18, _19: _2__19, }) => {
                    _0 == _2__0 && _1 == _2__1 && _2 == _2__2 && _3 == _2__3 && _4 == _2__4 && _5 == _2__5 && _6 == _2__6 && _7 == _2__7 && _8 == _2__8 && _9 == _2__9 && _10 == _2__10 && _11 == _2__11 && _12 == _2__12 && _13 == _2__13 && _14 == _2__14 && _15 == _2__15 && _16 == _2__16 && _17 == _2__17 && _18 == _2__18 && _19 == _2__19
                },
                _ => {
                    false
                },
            }
        }
    }

    impl<T0: DafnyType + Eq + Hash, T1: DafnyType + Eq + Hash, T2: DafnyType + Eq + Hash, T3: DafnyType + Eq + Hash, T4: DafnyType + Eq + Hash, T5: DafnyType + Eq + Hash, T6: DafnyType + Eq + Hash, T7: DafnyType + Eq + Hash, T8: DafnyType + Eq + Hash, T9: DafnyType + Eq + Hash, T10: DafnyType + Eq + Hash, T11: DafnyType + Eq + Hash, T12: DafnyType + Eq + Hash, T13: DafnyType + Eq + Hash, T14: DafnyType + Eq + Hash, T15: DafnyType + Eq + Hash, T16: DafnyType + Eq + Hash, T17: DafnyType + Eq + Hash, T18: DafnyType + Eq + Hash, T19: DafnyType + Eq + Hash> Eq
        for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {}

    impl<T0: DafnyType + Hash, T1: DafnyType + Hash, T2: DafnyType + Hash, T3: DafnyType + Hash, T4: DafnyType + Hash, T5: DafnyType + Hash, T6: DafnyType + Hash, T7: DafnyType + Hash, T8: DafnyType + Hash, T9: DafnyType + Hash, T10: DafnyType + Hash, T11: DafnyType + Hash, T12: DafnyType + Hash, T13: DafnyType + Hash, T14: DafnyType + Hash, T15: DafnyType + Hash, T16: DafnyType + Hash, T17: DafnyType + Hash, T18: DafnyType + Hash, T19: DafnyType + Hash> Hash
        for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
        fn hash<_H: Hasher>(&self, _state: &mut _H) {
            match self {
                Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => {
                    Hash::hash(_0, _state);
                    Hash::hash(_1, _state);
                    Hash::hash(_2, _state);
                    Hash::hash(_3, _state);
                    Hash::hash(_4, _state);
                    Hash::hash(_5, _state);
                    Hash::hash(_6, _state);
                    Hash::hash(_7, _state);
                    Hash::hash(_8, _state);
                    Hash::hash(_9, _state);
                    Hash::hash(_10, _state);
                    Hash::hash(_11, _state);
                    Hash::hash(_12, _state);
                    Hash::hash(_13, _state);
                    Hash::hash(_14, _state);
                    Hash::hash(_15, _state);
                    Hash::hash(_16, _state);
                    Hash::hash(_17, _state);
                    Hash::hash(_18, _state);
                    Hash::hash(_19, _state)
                },
            }
        }
    }

    impl<T0: DafnyType, T1: DafnyType, T2: DafnyType, T3: DafnyType, T4: DafnyType, T5: DafnyType, T6: DafnyType, T7: DafnyType, T8: DafnyType, T9: DafnyType, T10: DafnyType, T11: DafnyType, T12: DafnyType, T13: DafnyType, T14: DafnyType, T15: DafnyType, T16: DafnyType, T17: DafnyType, T18: DafnyType, T19: DafnyType> AsRef<Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>
        for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
        fn as_ref(&self) -> &Self {
            self
        }
    }
}