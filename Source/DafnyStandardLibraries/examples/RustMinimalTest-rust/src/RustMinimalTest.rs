#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
#![cfg_attr(any(), rustfmt::skip)]

pub mod _module {
    pub use ::dafny_runtime::Sequence;
    pub use ::dafny_runtime::DafnyChar;
    pub use ::dafny_runtime::DafnyPrintWrapper;
    pub use ::dafny_runtime::string_of;

    pub struct _default {}

    impl _default {
        pub fn _Test__Main_(_noArgsParameter: &Sequence<Sequence<DafnyChar>>) -> () {
            let mut success: bool = true;
            print!("{}", DafnyPrintWrapper(&string_of(r#"RustMinimalTest.TestBasicFunctionality: "#)));
            crate::RustMinimalTest::_default::TestBasicFunctionality();
            print!("{}", DafnyPrintWrapper(&string_of(r#"PASSED
"#)));
            if !success {
                panic!("Halt")
            };
            return ();
        }
    }
}
/// *****************************************************************************
///  Copyright by the contributors to the Dafny Project
///  SPDX-License-Identifier: MIT
/// *****************************************************************************
/// Source/DafnyStandardLibraries/examples/RustMinimalTest.dfy(7,1)
pub mod RustMinimalTest {
    pub use ::std::rc::Rc;
    pub use crate::Std::Wrappers::Result;
    pub use ::dafny_runtime::DafnyInt;
    pub use ::dafny_runtime::Sequence;
    pub use ::dafny_runtime::DafnyChar;
    pub use ::dafny_runtime::int;
    pub use crate::Std::Wrappers::Result::Success;
    pub use ::dafny_runtime::DafnyPrintWrapper;
    pub use ::dafny_runtime::string_of;
    pub use crate::Std::Wrappers::Result::Failure;

    pub struct _default {}

    impl _default {
        /// Source/DafnyStandardLibraries/examples/RustMinimalTest.dfy(10,3)
        pub fn TestBasicFunctionality() -> () {
            let mut result: Rc<Result<DafnyInt, Sequence<DafnyChar>>> = Rc::new(Result::Success::<DafnyInt, Sequence<DafnyChar>> {
                        value: int!(42)
                    });
            if !matches!((&result).as_ref(), Success{ .. }) {
                panic!("Halt")
            };
            let mut _e00: DafnyInt = result.value().clone();
            let mut _e10: DafnyInt = int!(42);
            if !(_e00.clone() == _e10.clone()) {
                print!("{}", DafnyPrintWrapper(&string_of("\nLeft:\n")));
                print!("{}", DafnyPrintWrapper(&_e00));
                print!("{}", DafnyPrintWrapper(&string_of("\nRight:\n")));
                print!("{}", DafnyPrintWrapper(&_e10));
                panic!("Halt")
            };
            let mut failure: Rc<Result<DafnyInt, Sequence<DafnyChar>>> = Rc::new(Result::Failure::<DafnyInt, Sequence<DafnyChar>> {
                        error: string_of("error")
                    });
            if !matches!((&failure).as_ref(), Failure{ .. }) {
                panic!("Halt")
            };
            let mut _e01: Sequence<DafnyChar> = failure.error().clone();
            let mut _e11: Sequence<DafnyChar> = string_of("error");
            if !(_e01.clone() == _e11.clone()) {
                print!("{}", DafnyPrintWrapper(&string_of("\nLeft:\n")));
                print!("{}", DafnyPrintWrapper(&_e01));
                print!("{}", DafnyPrintWrapper(&string_of("\nRight:\n")));
                print!("{}", DafnyPrintWrapper(&_e11));
                panic!("Halt")
            };
            print!("{}", DafnyPrintWrapper(&string_of("Rust standard library basic test: PASSED\n")));
            return ();
        }
    }

    /// Source/DafnyStandardLibraries/examples/RustMinimalTest.dfy(10,3)
    #[test]
    pub fn TestBasicFunctionality() {
        _default::TestBasicFunctionality()
    }
}
pub mod Std {
    /// DafnyStandardLibraries-rs.dfy(4,1)
    pub mod Wrappers {
        pub use ::dafny_runtime::DafnyType;
        pub use ::std::rc::Rc;
        pub use crate::Std::Wrappers::Option::None;
        pub use ::std::fmt::Debug;
        pub use ::std::fmt::Formatter;
        pub use ::dafny_runtime::DafnyPrint;
        pub use ::std::cmp::Eq;
        pub use ::std::hash::Hash;
        pub use ::std::cmp::PartialEq;
        pub use ::std::hash::Hasher;
        pub use ::std::convert::AsRef;
        pub use crate::Std::Wrappers::Result::Failure;
        pub use crate::Std::Wrappers::Result::Success;
        pub use crate::Std::Wrappers::Outcome::Fail;
        pub use crate::Std::Wrappers::Outcome::Pass;
        pub use crate::Std::Wrappers::OutcomeResult::_Fail_k;

        pub struct _default {}

        impl _default {
            /// DafnyStandardLibraries-rs.dfy(5,3)
            pub fn Need<_E: DafnyType>(condition: bool, error: &_E) -> Rc<crate::Std::Wrappers::OutcomeResult<_E>> {
                if condition {
                    Rc::new(crate::Std::Wrappers::OutcomeResult::_Pass_k::<_E> {})
                } else {
                    Rc::new(crate::Std::Wrappers::OutcomeResult::_Fail_k::<_E> {
                            error: error.clone()
                        })
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(13,3)
        #[derive(Clone)]
        pub enum Option<T: DafnyType> {
            None {},
            Some {
                value: T
            }
        }

        impl<T: DafnyType> Option<T> {
            /// DafnyStandardLibraries-rs.dfy(14,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), None{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(19,5)
            pub fn PropagateFailure<_U: DafnyType>(&self) -> Rc<crate::Std::Wrappers::Option<_U>> {
                Rc::new(crate::Std::Wrappers::Option::None::<_U> {})
            }
            /// DafnyStandardLibraries-rs.dfy(25,5)
            pub fn Extract(&self) -> T {
                self.value().clone()
            }
            /// DafnyStandardLibraries-rs.dfy(31,5)
            pub fn GetOr(&self, default: &T) -> T {
                let mut _source0: Rc<crate::Std::Wrappers::Option<T>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), None{ .. }) {
                    default.clone()
                } else {
                    let mut ___mcc_h0: T = _source0.value().clone();
                    let mut v: T = ___mcc_h0.clone();
                    v.clone()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(40,5)
            pub fn ToResult<_E: DafnyType>(&self, error: &_E) -> Rc<crate::Std::Wrappers::Result<T, _E>> {
                let mut _source0: Rc<crate::Std::Wrappers::Option<T>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), None{ .. }) {
                    Rc::new(crate::Std::Wrappers::Result::Failure::<T, _E> {
                            error: error.clone()
                        })
                } else {
                    let mut ___mcc_h0: T = _source0.value().clone();
                    let mut v: T = ___mcc_h0.clone();
                    Rc::new(crate::Std::Wrappers::Result::Success::<T, _E> {
                            value: v.clone()
                        })
                }
            }
            /// DafnyStandardLibraries-rs.dfy(49,5)
            pub fn ToOutcome<_E: DafnyType>(&self, error: &_E) -> Rc<crate::Std::Wrappers::Outcome<_E>> {
                let mut _source0: Rc<crate::Std::Wrappers::Option<T>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), None{ .. }) {
                    Rc::new(crate::Std::Wrappers::Outcome::Fail::<_E> {
                            error: error.clone()
                        })
                } else {
                    let mut ___mcc_h0: T = _source0.value().clone();
                    let mut v: T = ___mcc_h0.clone();
                    Rc::new(crate::Std::Wrappers::Outcome::Pass::<_E> {})
                }
            }
            /// DafnyStandardLibraries-rs.dfy(58,5)
            pub fn Map<_FC: DafnyType>(&self, rewrap: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Wrappers::Option<T>>) -> _FC>) -> _FC {
                rewrap(&Rc::new(self.clone()))
            }
            /// Gets the field value for all enum members which have it
            pub fn value(&self) -> &T {
                match self {
                    Option::None{} => panic!("field does not exist on this variant"),
                    Option::Some{value, } => value,
                }
            }
        }

        impl<T: DafnyType> Debug
            for Option<T> {
            fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                DafnyPrint::fmt_print(self, f, true)
            }
        }

        impl<T: DafnyType> DafnyPrint
            for Option<T> {
            fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                match self {
                    Option::None{} => {
                        write!(_formatter, "Std.Wrappers.Option.None")?;
                        Ok(())
                    },
                    Option::Some{value, } => {
                        write!(_formatter, "Std.Wrappers.Option.Some(")?;
                        DafnyPrint::fmt_print(value, _formatter, false)?;
                        write!(_formatter, ")")?;
                        Ok(())
                    },
                }
            }
        }

        impl<T: DafnyType> Option<T> {
            /// Given type parameter conversions, returns a lambda to convert this structure
            pub fn coerce<__T0: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T) -> __T0 + 'static>) -> Rc<impl ::std::ops::Fn(Option<T>) -> Option<__T0>> {
                Rc::new(move |this: Self| -> Option<__T0>{
                        match this {
                            Option::None{} => {
                                Option::None {}
                            },
                            Option::Some{value, } => {
                                Option::Some {
                                    value: f_0.clone()(value)
                                }
                            },
                        }
                    })
            }
        }

        impl<T: DafnyType + Eq + Hash> PartialEq
            for Option<T> {
            fn eq(&self, other: &Self) -> bool {
                match (
                        self,
                        other
                    ) {
                    (Option::None{}, Option::None{}) => {
                        true
                    },
                    (Option::Some{value, }, Option::Some{value: _2_value, }) => {
                        value == _2_value
                    },
                    _ => {
                        false
                    },
                }
            }
        }

        impl<T: DafnyType + Eq + Hash> Eq
            for Option<T> {}

        impl<T: DafnyType + Hash> Hash
            for Option<T> {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                match self {
                    Option::None{} => {
                        
                    },
                    Option::Some{value, } => {
                        Hash::hash(value, _state)
                    },
                }
            }
        }

        impl<T: DafnyType> AsRef<Option<T>>
            for Option<T> {
            fn as_ref(&self) -> &Self {
                self
            }
        }

        /// DafnyStandardLibraries-rs.dfy(64,3)
        #[derive(Clone)]
        pub enum Result<R: DafnyType, E: DafnyType> {
            Success {
                value: R
            },
            Failure {
                error: E
            }
        }

        impl<R: DafnyType, E: DafnyType> Result<R, E> {
            /// DafnyStandardLibraries-rs.dfy(65,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), Failure{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(70,5)
            pub fn PropagateFailure<_U: DafnyType>(&self) -> Rc<crate::Std::Wrappers::Result<_U, E>> {
                Rc::new(crate::Std::Wrappers::Result::Failure::<_U, E> {
                        error: self.error().clone()
                    })
            }
            /// DafnyStandardLibraries-rs.dfy(76,5)
            pub fn Extract(&self) -> R {
                self.value().clone()
            }
            /// DafnyStandardLibraries-rs.dfy(82,5)
            pub fn GetOr(&self, default: &R) -> R {
                let mut _source0: Rc<crate::Std::Wrappers::Result<R, E>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), Success{ .. }) {
                    let mut ___mcc_h0: R = _source0.value().clone();
                    let mut s: R = ___mcc_h0.clone();
                    s.clone()
                } else {
                    let mut ___mcc_h1: E = _source0.error().clone();
                    let mut e: E = ___mcc_h1.clone();
                    default.clone()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(91,5)
            pub fn ToOption(&self) -> Rc<crate::Std::Wrappers::Option<R>> {
                let mut _source0: Rc<crate::Std::Wrappers::Result<R, E>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), Success{ .. }) {
                    let mut ___mcc_h0: R = _source0.value().clone();
                    let mut s: R = ___mcc_h0.clone();
                    Rc::new(crate::Std::Wrappers::Option::Some::<R> {
                            value: s.clone()
                        })
                } else {
                    let mut ___mcc_h1: E = _source0.error().clone();
                    let mut e: E = ___mcc_h1.clone();
                    Rc::new(crate::Std::Wrappers::Option::None::<R> {})
                }
            }
            /// DafnyStandardLibraries-rs.dfy(100,5)
            pub fn ToOutcome(&self) -> Rc<crate::Std::Wrappers::Outcome<E>> {
                let mut _source0: Rc<crate::Std::Wrappers::Result<R, E>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), Success{ .. }) {
                    let mut ___mcc_h0: R = _source0.value().clone();
                    let mut s: R = ___mcc_h0.clone();
                    Rc::new(crate::Std::Wrappers::Outcome::Pass::<E> {})
                } else {
                    let mut ___mcc_h1: E = _source0.error().clone();
                    let mut e: E = ___mcc_h1.clone();
                    Rc::new(crate::Std::Wrappers::Outcome::Fail::<E> {
                            error: e.clone()
                        })
                }
            }
            /// DafnyStandardLibraries-rs.dfy(109,5)
            pub fn Map<_FC: DafnyType>(&self, rewrap: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Wrappers::Result<R, E>>) -> _FC>) -> _FC {
                rewrap(&Rc::new(self.clone()))
            }
            /// DafnyStandardLibraries-rs.dfy(114,5)
            pub fn MapFailure<_NewE: DafnyType>(&self, reWrap: &Rc<dyn ::std::ops::Fn(&E) -> _NewE>) -> Rc<crate::Std::Wrappers::Result<R, _NewE>> {
                let mut _source0: Rc<crate::Std::Wrappers::Result<R, E>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), Success{ .. }) {
                    let mut ___mcc_h0: R = _source0.value().clone();
                    let mut s: R = ___mcc_h0.clone();
                    Rc::new(crate::Std::Wrappers::Result::Success::<R, _NewE> {
                            value: s.clone()
                        })
                } else {
                    let mut ___mcc_h1: E = _source0.error().clone();
                    let mut e: E = ___mcc_h1.clone();
                    Rc::new(crate::Std::Wrappers::Result::Failure::<R, _NewE> {
                            error: reWrap(&e)
                        })
                }
            }
            /// Gets the field value for all enum members which have it
            pub fn value(&self) -> &R {
                match self {
                    Result::Success{value, } => value,
                    Result::Failure{error, } => panic!("field does not exist on this variant"),
                }
            }
            /// Gets the field error for all enum members which have it
            pub fn error(&self) -> &E {
                match self {
                    Result::Success{value, } => panic!("field does not exist on this variant"),
                    Result::Failure{error, } => error,
                }
            }
        }

        impl<R: DafnyType, E: DafnyType> Debug
            for Result<R, E> {
            fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                DafnyPrint::fmt_print(self, f, true)
            }
        }

        impl<R: DafnyType, E: DafnyType> DafnyPrint
            for Result<R, E> {
            fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                match self {
                    Result::Success{value, } => {
                        write!(_formatter, "Std.Wrappers.Result.Success(")?;
                        DafnyPrint::fmt_print(value, _formatter, false)?;
                        write!(_formatter, ")")?;
                        Ok(())
                    },
                    Result::Failure{error, } => {
                        write!(_formatter, "Std.Wrappers.Result.Failure(")?;
                        DafnyPrint::fmt_print(error, _formatter, false)?;
                        write!(_formatter, ")")?;
                        Ok(())
                    },
                }
            }
        }

        impl<R: DafnyType, E: DafnyType> Result<R, E> {
            /// Given type parameter conversions, returns a lambda to convert this structure
            pub fn coerce<__T0: DafnyType, __T1: DafnyType>(f_0: Rc<impl ::std::ops::Fn(R) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(E) -> __T1 + 'static>) -> Rc<impl ::std::ops::Fn(Result<R, E>) -> Result<__T0, __T1>> {
                Rc::new(move |this: Self| -> Result<__T0, __T1>{
                        match this {
                            Result::Success{value, } => {
                                Result::Success {
                                    value: f_0.clone()(value)
                                }
                            },
                            Result::Failure{error, } => {
                                Result::Failure {
                                    error: f_1.clone()(error)
                                }
                            },
                        }
                    })
            }
        }

        impl<R: DafnyType + Eq + Hash, E: DafnyType + Eq + Hash> PartialEq
            for Result<R, E> {
            fn eq(&self, other: &Self) -> bool {
                match (
                        self,
                        other
                    ) {
                    (Result::Success{value, }, Result::Success{value: _2_value, }) => {
                        value == _2_value
                    },
                    (Result::Failure{error, }, Result::Failure{error: _2_error, }) => {
                        error == _2_error
                    },
                    _ => {
                        false
                    },
                }
            }
        }

        impl<R: DafnyType + Eq + Hash, E: DafnyType + Eq + Hash> Eq
            for Result<R, E> {}

        impl<R: DafnyType + Hash, E: DafnyType + Hash> Hash
            for Result<R, E> {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                match self {
                    Result::Success{value, } => {
                        Hash::hash(value, _state)
                    },
                    Result::Failure{error, } => {
                        Hash::hash(error, _state)
                    },
                }
            }
        }

        impl<R: DafnyType, E: DafnyType> AsRef<Result<R, E>>
            for Result<R, E> {
            fn as_ref(&self) -> &Self {
                self
            }
        }

        /// DafnyStandardLibraries-rs.dfy(124,3)
        #[derive(Clone)]
        pub enum Outcome<E: DafnyType> {
            Pass {},
            Fail {
                error: E
            }
        }

        impl<E: DafnyType> Outcome<E> {
            /// DafnyStandardLibraries-rs.dfy(125,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), Fail{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(130,5)
            pub fn PropagateFailure(&self) -> Rc<crate::Std::Wrappers::Outcome<E>> {
                Rc::new(self.clone())
            }
            /// DafnyStandardLibraries-rs.dfy(136,5)
            pub fn ToOption<_R: DafnyType>(&self, r: &_R) -> Rc<crate::Std::Wrappers::Option<_R>> {
                let mut _source0: Rc<crate::Std::Wrappers::Outcome<E>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), Pass{ .. }) {
                    Rc::new(crate::Std::Wrappers::Option::Some::<_R> {
                            value: r.clone()
                        })
                } else {
                    let mut ___mcc_h0: E = _source0.error().clone();
                    let mut e: E = ___mcc_h0.clone();
                    Rc::new(crate::Std::Wrappers::Option::None::<_R> {})
                }
            }
            /// DafnyStandardLibraries-rs.dfy(145,5)
            pub fn ToResult<_R: DafnyType>(&self, r: &_R) -> Rc<crate::Std::Wrappers::Result<_R, E>> {
                let mut _source0: Rc<crate::Std::Wrappers::Outcome<E>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), Pass{ .. }) {
                    Rc::new(crate::Std::Wrappers::Result::Success::<_R, E> {
                            value: r.clone()
                        })
                } else {
                    let mut ___mcc_h0: E = _source0.error().clone();
                    let mut e: E = ___mcc_h0.clone();
                    Rc::new(crate::Std::Wrappers::Result::Failure::<_R, E> {
                            error: e.clone()
                        })
                }
            }
            /// DafnyStandardLibraries-rs.dfy(154,5)
            pub fn Map<_FC: DafnyType>(&self, rewrap: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Wrappers::Outcome<E>>) -> _FC>) -> _FC {
                rewrap(&Rc::new(self.clone()))
            }
            /// DafnyStandardLibraries-rs.dfy(159,5)
            pub fn MapFailure<_T: DafnyType, _NewE: DafnyType>(&self, rewrap: &Rc<dyn ::std::ops::Fn(&E) -> _NewE>, default: &_T) -> Rc<crate::Std::Wrappers::Result<_T, _NewE>> {
                let mut _source0: Rc<crate::Std::Wrappers::Outcome<E>> = Rc::new(self.clone());
                if matches!((&_source0).as_ref(), Pass{ .. }) {
                    Rc::new(crate::Std::Wrappers::Result::Success::<_T, _NewE> {
                            value: default.clone()
                        })
                } else {
                    let mut ___mcc_h0: E = _source0.error().clone();
                    let mut e: E = ___mcc_h0.clone();
                    Rc::new(crate::Std::Wrappers::Result::Failure::<_T, _NewE> {
                            error: rewrap(&e)
                        })
                }
            }
            /// DafnyStandardLibraries-rs.dfy(168,5)
            pub fn Need(condition: bool, error: &E) -> Rc<crate::Std::Wrappers::Outcome<E>> {
                if condition {
                    Rc::new(crate::Std::Wrappers::Outcome::Pass::<E> {})
                } else {
                    Rc::new(crate::Std::Wrappers::Outcome::Fail::<E> {
                            error: error.clone()
                        })
                }
            }
            /// Gets the field error for all enum members which have it
            pub fn error(&self) -> &E {
                match self {
                    Outcome::Pass{} => panic!("field does not exist on this variant"),
                    Outcome::Fail{error, } => error,
                }
            }
        }

        impl<E: DafnyType> Debug
            for Outcome<E> {
            fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                DafnyPrint::fmt_print(self, f, true)
            }
        }

        impl<E: DafnyType> DafnyPrint
            for Outcome<E> {
            fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                match self {
                    Outcome::Pass{} => {
                        write!(_formatter, "Std.Wrappers.Outcome.Pass")?;
                        Ok(())
                    },
                    Outcome::Fail{error, } => {
                        write!(_formatter, "Std.Wrappers.Outcome.Fail(")?;
                        DafnyPrint::fmt_print(error, _formatter, false)?;
                        write!(_formatter, ")")?;
                        Ok(())
                    },
                }
            }
        }

        impl<E: DafnyType> Outcome<E> {
            /// Given type parameter conversions, returns a lambda to convert this structure
            pub fn coerce<__T0: DafnyType>(f_0: Rc<impl ::std::ops::Fn(E) -> __T0 + 'static>) -> Rc<impl ::std::ops::Fn(Outcome<E>) -> Outcome<__T0>> {
                Rc::new(move |this: Self| -> Outcome<__T0>{
                        match this {
                            Outcome::Pass{} => {
                                Outcome::Pass {}
                            },
                            Outcome::Fail{error, } => {
                                Outcome::Fail {
                                    error: f_0.clone()(error)
                                }
                            },
                        }
                    })
            }
        }

        impl<E: DafnyType + Eq + Hash> PartialEq
            for Outcome<E> {
            fn eq(&self, other: &Self) -> bool {
                match (
                        self,
                        other
                    ) {
                    (Outcome::Pass{}, Outcome::Pass{}) => {
                        true
                    },
                    (Outcome::Fail{error, }, Outcome::Fail{error: _2_error, }) => {
                        error == _2_error
                    },
                    _ => {
                        false
                    },
                }
            }
        }

        impl<E: DafnyType + Eq + Hash> Eq
            for Outcome<E> {}

        impl<E: DafnyType + Hash> Hash
            for Outcome<E> {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                match self {
                    Outcome::Pass{} => {
                        
                    },
                    Outcome::Fail{error, } => {
                        Hash::hash(error, _state)
                    },
                }
            }
        }

        impl<E: DafnyType> AsRef<Outcome<E>>
            for Outcome<E> {
            fn as_ref(&self) -> &Self {
                self
            }
        }

        /// DafnyStandardLibraries-rs.dfy(177,3)
        #[derive(Clone)]
        pub enum OutcomeResult<E: DafnyType> {
            _Pass_k {},
            _Fail_k {
                error: E
            }
        }

        impl<E: DafnyType> OutcomeResult<E> {
            /// DafnyStandardLibraries-rs.dfy(178,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), _Fail_k{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(183,5)
            pub fn PropagateFailure<_U: DafnyType>(&self) -> Rc<crate::Std::Wrappers::Result<_U, E>> {
                Rc::new(crate::Std::Wrappers::Result::Failure::<_U, E> {
                        error: self.error().clone()
                    })
            }
            /// Gets the field error for all enum members which have it
            pub fn error(&self) -> &E {
                match self {
                    OutcomeResult::_Pass_k{} => panic!("field does not exist on this variant"),
                    OutcomeResult::_Fail_k{error, } => error,
                }
            }
        }

        impl<E: DafnyType> Debug
            for OutcomeResult<E> {
            fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                DafnyPrint::fmt_print(self, f, true)
            }
        }

        impl<E: DafnyType> DafnyPrint
            for OutcomeResult<E> {
            fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                match self {
                    OutcomeResult::_Pass_k{} => {
                        write!(_formatter, "Std.Wrappers.OutcomeResult.Pass_k")?;
                        Ok(())
                    },
                    OutcomeResult::_Fail_k{error, } => {
                        write!(_formatter, "Std.Wrappers.OutcomeResult.Fail_k(")?;
                        DafnyPrint::fmt_print(error, _formatter, false)?;
                        write!(_formatter, ")")?;
                        Ok(())
                    },
                }
            }
        }

        impl<E: DafnyType> OutcomeResult<E> {
            /// Given type parameter conversions, returns a lambda to convert this structure
            pub fn coerce<__T0: DafnyType>(f_0: Rc<impl ::std::ops::Fn(E) -> __T0 + 'static>) -> Rc<impl ::std::ops::Fn(OutcomeResult<E>) -> OutcomeResult<__T0>> {
                Rc::new(move |this: Self| -> OutcomeResult<__T0>{
                        match this {
                            OutcomeResult::_Pass_k{} => {
                                OutcomeResult::_Pass_k {}
                            },
                            OutcomeResult::_Fail_k{error, } => {
                                OutcomeResult::_Fail_k {
                                    error: f_0.clone()(error)
                                }
                            },
                        }
                    })
            }
        }

        impl<E: DafnyType + Eq + Hash> PartialEq
            for OutcomeResult<E> {
            fn eq(&self, other: &Self) -> bool {
                match (
                        self,
                        other
                    ) {
                    (OutcomeResult::_Pass_k{}, OutcomeResult::_Pass_k{}) => {
                        true
                    },
                    (OutcomeResult::_Fail_k{error, }, OutcomeResult::_Fail_k{error: _2_error, }) => {
                        error == _2_error
                    },
                    _ => {
                        false
                    },
                }
            }
        }

        impl<E: DafnyType + Eq + Hash> Eq
            for OutcomeResult<E> {}

        impl<E: DafnyType + Hash> Hash
            for OutcomeResult<E> {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                match self {
                    OutcomeResult::_Pass_k{} => {
                        
                    },
                    OutcomeResult::_Fail_k{error, } => {
                        Hash::hash(error, _state)
                    },
                }
            }
        }

        impl<E: DafnyType> AsRef<OutcomeResult<E>>
            for OutcomeResult<E> {
            fn as_ref(&self) -> &Self {
                self
            }
        }
    }
}
fn main() {
  let args: Vec<String> = ::std::env::args().collect();
  let dafny_args =
    ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(
    &args, |s| 
  ::dafny_runtime::dafny_runtime_conversions::unicode_chars_true::string_to_dafny_string(s));
  crate::_module::_default::_Test__Main_(&dafny_args);
}