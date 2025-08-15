#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
#![cfg_attr(any(), rustfmt::skip)]

pub mod _module {
    
}
/// *****************************************************************************
///  Copyright by the contributors to the Dafny Project
///  SPDX-License-Identifier: MIT
/// *****************************************************************************
/// Source/DafnyStandardLibraries/examples/SimpleTest.dfy(7,1)
pub mod SimpleTest {
    pub use ::dafny_runtime::Sequence;
    pub use ::dafny_runtime::DafnyChar;
    pub use ::std::rc::Rc;
    pub use crate::Std::Wrappers::Result;
    pub use ::dafny_runtime::DafnyInt;
    pub use ::dafny_runtime::int;
    pub use crate::Std::Wrappers::Result::Success;
    pub use ::dafny_runtime::DafnyPrintWrapper;
    pub use ::dafny_runtime::string_of;

    pub struct _default {}

    impl _default {
        /// Source/DafnyStandardLibraries/examples/SimpleTest.dfy(10,3)
        pub fn Main(_noArgsParameter: &Sequence<Sequence<DafnyChar>>) -> () {
            let mut result: Rc<Result<DafnyInt, Sequence<DafnyChar>>> = Rc::new(Result::Success::<DafnyInt, Sequence<DafnyChar>> {
                        value: int!(42)
                    });
            let mut _source0: Rc<Result<DafnyInt, Sequence<DafnyChar>>> = result.clone();
            if matches!((&_source0).as_ref(), Success{ .. }) {
                let mut ___mcc_h0: DafnyInt = _source0.value().clone();
                let mut value: DafnyInt = ___mcc_h0.clone();
                print!("{}", DafnyPrintWrapper(&string_of("Success: ")));
                print!("{}", DafnyPrintWrapper(&value));
                print!("{}", DafnyPrintWrapper(&string_of("\n")));
                print!("{}", DafnyPrintWrapper(&string_of("Simple test: PASSED\n")))
            } else {
                let mut ___mcc_h1: Sequence<DafnyChar> = _source0.error().clone();
                let mut error: Sequence<DafnyChar> = ___mcc_h1.clone();
                print!("{}", DafnyPrintWrapper(&string_of("Failure: ")));
                print!("{}", DafnyPrintWrapper(&error));
                print!("{}", DafnyPrintWrapper(&string_of("\n")));
                print!("{}", DafnyPrintWrapper(&string_of("Simple test: FAILED\n")))
            };
            return ();
        }
    }
}
pub mod Std {
    pub mod Arithmetic {
        /// DafnyStandardLibraries-rs.dfy(1883,1)
        pub mod DivInternals {
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::int;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(1885,3)
                pub fn DivPos(x: &DafnyInt, d: &DafnyInt) -> DafnyInt {
                    let mut _accumulator: DafnyInt = int!(0);
                    let mut _r0 = x.clone();
                    let mut _r1 = d.clone();
                    'TAIL_CALL_START: loop {
                        let x = _r0;
                        let d = _r1;
                        if x.clone() < int!(0) {
                            _accumulator = _accumulator.clone() + int!(-1);
                            let mut _in0: DafnyInt = x.clone() + d.clone();
                            let mut _in1: DafnyInt = d.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        } else {
                            if x.clone() < d.clone() {
                                return int!(0) + _accumulator.clone();
                            } else {
                                _accumulator = _accumulator.clone() + int!(1);
                                let mut _in2: DafnyInt = x.clone() - d.clone();
                                let mut _in3: DafnyInt = d.clone();
                                _r0 = _in2.clone();
                                _r1 = _in3.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(1897,3)
                pub fn DivRecursive(x: &DafnyInt, d: &DafnyInt) -> DafnyInt {
                    if int!(0) < d.clone() {
                        crate::Std::Arithmetic::DivInternals::_default::DivPos(x, d)
                    } else {
                        int!(-1) * crate::Std::Arithmetic::DivInternals::_default::DivPos(x, &(int!(-1) * d.clone()))
                    }
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(2082,1)
        pub mod DivInternalsNonlinear {
            
        }

        /// DafnyStandardLibraries-rs.dfy(193,1)
        pub mod DivMod {
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::euclidian_modulo;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(1353,3)
                pub fn MultiplesVanish(a: &DafnyInt, b: &DafnyInt, m: &DafnyInt) -> bool {
                    euclidian_modulo(m.clone() * a.clone() + b.clone(), m.clone()) == euclidian_modulo(b.clone(), m.clone())
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(2108,1)
        pub mod GeneralInternals {
            
        }

        /// DafnyStandardLibraries-rs.dfy(3289,1)
        pub mod Logarithm {
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::euclidian_division;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(3291,3)
                pub fn Log(base: &nat, pow: &nat) -> nat {
                    let mut _accumulator: nat = int!(0);
                    let mut _r0 = base.clone();
                    let mut _r1 = pow.clone();
                    'TAIL_CALL_START: loop {
                        let base = _r0;
                        let pow = _r1;
                        if pow.clone() < base.clone() {
                            return int!(0) + _accumulator.clone();
                        } else {
                            _accumulator = _accumulator.clone() + int!(1);
                            let mut _in0: nat = base.clone();
                            let mut _in1: DafnyInt = euclidian_division(pow.clone(), base.clone());
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(2133,1)
        pub mod ModInternals {
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::int;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(2135,3)
                pub fn ModRecursive(x: &DafnyInt, d: &DafnyInt) -> DafnyInt {
                    let mut _r0 = x.clone();
                    let mut _r1 = d.clone();
                    'TAIL_CALL_START: loop {
                        let x = _r0;
                        let d = _r1;
                        if x.clone() < int!(0) {
                            let mut _in0: DafnyInt = d.clone() + x.clone();
                            let mut _in1: DafnyInt = d.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        } else {
                            if x.clone() < d.clone() {
                                return x.clone();
                            } else {
                                let mut _in2: DafnyInt = x.clone() - d.clone();
                                let mut _in3: DafnyInt = d.clone();
                                _r0 = _in2.clone();
                                _r1 = _in3.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(2522,1)
        pub mod ModInternalsNonlinear {
            
        }

        /// DafnyStandardLibraries-rs.dfy(3383,1)
        pub mod Mul {
            
        }

        /// DafnyStandardLibraries-rs.dfy(2554,1)
        pub mod MulInternals {
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::int;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(2556,3)
                pub fn MulPos(x: &DafnyInt, y: &DafnyInt) -> DafnyInt {
                    let mut _accumulator: DafnyInt = int!(0);
                    let mut _r0 = x.clone();
                    let mut _r1 = y.clone();
                    'TAIL_CALL_START: loop {
                        let x = _r0;
                        let y = _r1;
                        if x.clone() == int!(0) {
                            return int!(0) + _accumulator.clone();
                        } else {
                            _accumulator = _accumulator.clone() + y.clone();
                            let mut _in0: DafnyInt = x.clone() - int!(1);
                            let mut _in1: DafnyInt = y.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(2565,3)
                pub fn MulRecursive(x: &DafnyInt, y: &DafnyInt) -> DafnyInt {
                    if !(x.clone() < int!(0)) {
                        crate::Std::Arithmetic::MulInternals::_default::MulPos(x, y)
                    } else {
                        int!(-1) * crate::Std::Arithmetic::MulInternals::_default::MulPos(&(int!(-1) * x.clone()), y)
                    }
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(2686,1)
        pub mod MulInternalsNonlinear {
            
        }

        /// DafnyStandardLibraries-rs.dfy(3994,1)
        pub mod Power {
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::int;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(3996,3)
                pub fn Pow(b: &DafnyInt, e: &nat) -> DafnyInt {
                    let mut _accumulator: DafnyInt = int!(1);
                    let mut _r0 = b.clone();
                    let mut _r1 = e.clone();
                    'TAIL_CALL_START: loop {
                        let b = _r0;
                        let e = _r1;
                        if e.clone() == int!(0) {
                            return int!(1) * _accumulator.clone();
                        } else {
                            _accumulator = _accumulator.clone() * b.clone();
                            let mut _in0: DafnyInt = b.clone();
                            let mut _in1: DafnyInt = e.clone() - int!(1);
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(3893,1)
        pub mod Power2 {
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::int;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(3894,3)
                pub fn Pow2(e: &nat) -> nat {
                    crate::Std::Arithmetic::Power::_default::Pow(&int!(2), e)
                }
            }
        }
    }

    /// DafnyStandardLibraries-rs.dfy(4623,1)
    pub mod Base64 {
        pub use ::dafny_runtime::DafnyChar;
        pub use ::std::primitive::char;
        pub use ::dafny_runtime::Sequence;
        pub use ::dafny_runtime::euclidian_modulo;
        pub use ::dafny_runtime::int;
        pub use ::dafny_runtime::itertools::Itertools;
        pub use ::std::rc::Rc;
        pub use ::dafny_runtime::NumCast;
        pub use ::dafny_runtime::truncate;
        pub use ::dafny_runtime::seq;
        pub use ::dafny_runtime::MaybePlacebo;
        pub use ::dafny_runtime::DafnyInt;
        pub use ::dafny_runtime::euclidian_division;
        pub use ::dafny_runtime::Object;
        pub use ::dafny_runtime::_System::nat;
        pub use ::std::mem::MaybeUninit;
        pub use ::dafny_runtime::array;
        pub use ::dafny_runtime::DafnyUsize;
        pub use ::dafny_runtime::integer_range;
        pub use ::dafny_runtime::rd;
        pub use ::dafny_runtime::Zero;
        pub use crate::Std::Wrappers::Result;
        pub use ::dafny_runtime::string_of;

        pub struct _default {}

        impl _default {
            /// DafnyStandardLibraries-rs.dfy(4624,3)
            pub fn IsBase64Char(c: &DafnyChar) -> bool {
                c.clone() == DafnyChar(char::from_u32(43).unwrap()) || c.clone() == DafnyChar(char::from_u32(47).unwrap()) || !(c.clone() < DafnyChar(char::from_u32(48).unwrap())) && !(DafnyChar(char::from_u32(57).unwrap()) < c.clone()) || !(c.clone() < DafnyChar(char::from_u32(65).unwrap())) && !(DafnyChar(char::from_u32(90).unwrap()) < c.clone()) || !(c.clone() < DafnyChar(char::from_u32(97).unwrap())) && !(DafnyChar(char::from_u32(122).unwrap()) < c.clone())
            }
            /// DafnyStandardLibraries-rs.dfy(4635,3)
            pub fn IsUnpaddedBase64String(s: &Sequence<DafnyChar>) -> bool {
                euclidian_modulo(s.cardinality(), int!(4)) == int!(0) && Itertools::unique(s.iter()).all(({
                        let mut s = s.clone();
                        Rc::new(move |__forall_var_0: DafnyChar| -> bool{
            let mut k: DafnyChar = __forall_var_0.clone();
            !s.contains(&k) || crate::Std::Base64::_default::IsBase64Char(&k)
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                    }).as_ref())
            }
            /// DafnyStandardLibraries-rs.dfy(4643,3)
            pub fn IndexToChar(i: u8) -> DafnyChar {
                if i == 63 as u8 {
                    DafnyChar(char::from_u32(47).unwrap())
                } else {
                    if i == 62 as u8 {
                        DafnyChar(char::from_u32(43).unwrap())
                    } else {
                        if !(i < 52 as u8) && !((61 as u8) < i) {
                            DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(i - 4 as u8)).unwrap()).unwrap())
                        } else {
                            if !(i < 26 as u8) && !((51 as u8) < i) {
                                DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(i)).unwrap()).unwrap()) + DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(71)).unwrap()).unwrap())
                            } else {
                                DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(i)).unwrap()).unwrap()) + DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(65)).unwrap()).unwrap())
                            }
                        }
                    }
                }
            }
            /// DafnyStandardLibraries-rs.dfy(4663,3)
            pub fn CharToIndex(c: &DafnyChar) -> u8 {
                if c.clone() == DafnyChar(char::from_u32(47).unwrap()) {
                    63 as u8
                } else {
                    if c.clone() == DafnyChar(char::from_u32(43).unwrap()) {
                        62 as u8
                    } else {
                        if !(c.clone() < DafnyChar(char::from_u32(48).unwrap())) && !(DafnyChar(char::from_u32(57).unwrap()) < c.clone()) {
                            truncate!(int!((c.clone() + DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(4)).unwrap()).unwrap())).0), u8)
                        } else {
                            if !(c.clone() < DafnyChar(char::from_u32(97).unwrap())) && !(DafnyChar(char::from_u32(122).unwrap()) < c.clone()) {
                                truncate!(int!((c.clone() - DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(71)).unwrap()).unwrap())).0), u8)
                            } else {
                                truncate!(int!((c.clone() - DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(65)).unwrap()).unwrap())).0), u8)
                            }
                        }
                    }
                }
            }
            /// DafnyStandardLibraries-rs.dfy(4737,3)
            pub fn BV24ToSeq(x: u32) -> Sequence<u8> {
                let mut b0: u8 = (x >> truncate!(int!(16), u8) & 255 as u32) as u8;
                let mut b1: u8 = (x >> truncate!(int!(8), u8) & 255 as u32) as u8;
                let mut b2: u8 = (x & 255 as u32) as u8;
                seq![b0, b1, b2]
            }
            /// DafnyStandardLibraries-rs.dfy(4746,3)
            pub fn SeqToBV24(x: &Sequence<u8>) -> u32 {
                (x.get(&int!(0)) as u32) << truncate!(int!(16), u8) | (x.get(&int!(1)) as u32) << truncate!(int!(8), u8) | x.get(&int!(2)) as u32
            }
            /// DafnyStandardLibraries-rs.dfy(4763,3)
            pub fn BV24ToIndexSeq(x: u32) -> Sequence<u8> {
                let mut b0: u8 = (x >> truncate!(int!(18), u8) & 63 as u32) as u8;
                let mut b1: u8 = (x >> truncate!(int!(12), u8) & 63 as u32) as u8;
                let mut b2: u8 = (x >> truncate!(int!(6), u8) & 63 as u32) as u8;
                let mut b3: u8 = (x & 63 as u32) as u8;
                seq![b0, b1, b2, b3]
            }
            /// DafnyStandardLibraries-rs.dfy(4773,3)
            pub fn IndexSeqToBV24(x: &Sequence<u8>) -> u32 {
                (x.get(&int!(0)) as u32) << truncate!(int!(18), u8) | (x.get(&int!(1)) as u32) << truncate!(int!(12), u8) | (x.get(&int!(2)) as u32) << truncate!(int!(6), u8) | x.get(&int!(3)) as u32
            }
            /// DafnyStandardLibraries-rs.dfy(4790,3)
            pub fn DecodeBlock(s: &Sequence<u8>) -> Sequence<u8> {
                crate::Std::Base64::_default::BV24ToSeq(crate::Std::Base64::_default::IndexSeqToBV24(s))
            }
            /// DafnyStandardLibraries-rs.dfy(4797,3)
            pub fn EncodeBlock(s: &Sequence<u8>) -> Sequence<u8> {
                crate::Std::Base64::_default::BV24ToIndexSeq(crate::Std::Base64::_default::SeqToBV24(s))
            }
            /// DafnyStandardLibraries-rs.dfy(4822,3)
            pub fn DecodeRecursively(s: &Sequence<u8>) -> Sequence<u8> {
                let mut b = MaybePlacebo::<Sequence<u8>>::new();
                let mut resultLength: DafnyInt = euclidian_division(s.cardinality(), int!(4)) * int!(3);
                let mut result = MaybePlacebo::<Object<[u8]>>::new();
                let mut _init0: Rc<dyn ::std::ops::Fn(&nat) -> u8> = {
                        Rc::new(move |i: &nat| -> u8{
            0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                    };
                let mut _nw0: Object<[MaybeUninit<u8>]> = array::placebos_usize_object::<u8>(DafnyUsize::into_usize(resultLength.clone()));
                for __i0_0 in integer_range(truncate!(int!(0), usize), rd!(_nw0.clone()).len()) {
                    {
                        let __idx0 = DafnyUsize::into_usize(__i0_0.clone());
                        ::dafny_runtime::md!(_nw0)[__idx0] = MaybeUninit::new((&_init0)(&int!(__i0_0.clone())));
                    }
                }
                result = MaybePlacebo::from(array::construct_object(_nw0.clone()));
                let mut i: DafnyInt = s.cardinality();
                let mut j: DafnyInt = resultLength.clone();
                while int!(0) < i.clone() {
                    i = i.clone() - int!(4);
                    j = j.clone() - int!(3);
                    let mut block: Sequence<u8> = crate::Std::Base64::_default::DecodeBlock(&s.slice(&i, &(i.clone() + int!(4))));
                    {
                        let __idx0 = DafnyUsize::into_usize(j.clone());
                        ::dafny_runtime::md!(result.read())[__idx0] = block.get(&int!(0));
                    };
                    {
                        let __idx0 = DafnyUsize::into_usize(j.clone() + int!(1));
                        ::dafny_runtime::md!(result.read())[__idx0] = block.get(&int!(1));
                    };
                    {
                        let __idx0 = DafnyUsize::into_usize(j.clone() + int!(2));
                        ::dafny_runtime::md!(result.read())[__idx0] = block.get(&int!(2));
                    }
                };
                b = MaybePlacebo::from(Sequence::from_array_object(&result.read()));
                return b.read();
            }
            /// DafnyStandardLibraries-rs.dfy(4879,3)
            pub fn EncodeRecursively(b: &Sequence<u8>) -> Sequence<u8> {
                let mut s = MaybePlacebo::<Sequence<u8>>::new();
                let mut resultLength: DafnyInt = euclidian_division(b.cardinality(), int!(3)) * int!(4);
                let mut result = MaybePlacebo::<Object<[u8]>>::new();
                let mut _init0: Rc<dyn ::std::ops::Fn(&nat) -> u8> = {
                        Rc::new(move |i: &nat| -> u8{
            0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                    };
                let mut _nw0: Object<[MaybeUninit<u8>]> = array::placebos_usize_object::<u8>(DafnyUsize::into_usize(resultLength.clone()));
                for __i0_0 in integer_range(truncate!(int!(0), usize), rd!(_nw0.clone()).len()) {
                    {
                        let __idx0 = DafnyUsize::into_usize(__i0_0.clone());
                        ::dafny_runtime::md!(_nw0)[__idx0] = MaybeUninit::new((&_init0)(&int!(__i0_0.clone())));
                    }
                }
                result = MaybePlacebo::from(array::construct_object(_nw0.clone()));
                let mut i: DafnyInt = b.cardinality();
                let mut j: DafnyInt = resultLength.clone();
                while int!(0) < i.clone() {
                    i = i.clone() - int!(3);
                    j = j.clone() - int!(4);
                    let mut block: Sequence<u8> = crate::Std::Base64::_default::EncodeBlock(&b.slice(&i, &(i.clone() + int!(3))));
                    {
                        let __idx0 = DafnyUsize::into_usize(j.clone());
                        ::dafny_runtime::md!(result.read())[__idx0] = block.get(&int!(0));
                    };
                    {
                        let __idx0 = DafnyUsize::into_usize(j.clone() + int!(1));
                        ::dafny_runtime::md!(result.read())[__idx0] = block.get(&int!(1));
                    };
                    {
                        let __idx0 = DafnyUsize::into_usize(j.clone() + int!(2));
                        ::dafny_runtime::md!(result.read())[__idx0] = block.get(&int!(2));
                    };
                    {
                        let __idx0 = DafnyUsize::into_usize(j.clone() + int!(3));
                        ::dafny_runtime::md!(result.read())[__idx0] = block.get(&int!(3));
                    }
                };
                s = MaybePlacebo::from(Sequence::from_array_object(&result.read()));
                return s.read();
            }
            /// DafnyStandardLibraries-rs.dfy(5018,3)
            pub fn FromCharsToIndices(s: &Sequence<DafnyChar>) -> Sequence<u8> {
                {
                    let _initializer = {
                            let s: Sequence<DafnyChar> = s.clone();
                            {
                                let mut s = s.clone();
                                Rc::new(move |i: &DafnyInt| -> u8{
            crate::Std::Base64::_default::CharToIndex(&s.get(i))
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        };
                    integer_range(Zero::zero(), s.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(5025,3)
            pub fn FromIndicesToChars(b: &Sequence<u8>) -> Sequence<DafnyChar> {
                {
                    let _initializer = {
                            let b: Sequence<u8> = b.clone();
                            {
                                let mut b = b.clone();
                                Rc::new(move |i: &DafnyInt| -> DafnyChar{
            crate::Std::Base64::_default::IndexToChar(b.get(i))
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        };
                    integer_range(Zero::zero(), b.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(5045,3)
            pub fn DecodeUnpadded(s: &Sequence<DafnyChar>) -> Sequence<u8> {
                crate::Std::Base64::_default::DecodeRecursively(&crate::Std::Base64::_default::FromCharsToIndices(s))
            }
            /// DafnyStandardLibraries-rs.dfy(5061,3)
            pub fn EncodeUnpadded(b: &Sequence<u8>) -> Sequence<DafnyChar> {
                crate::Std::Base64::_default::FromIndicesToChars(&crate::Std::Base64::_default::EncodeRecursively(b))
            }
            /// DafnyStandardLibraries-rs.dfy(5153,3)
            pub fn Is1Padding(s: &Sequence<DafnyChar>) -> bool {
                s.cardinality() == int!(4) && crate::Std::Base64::_default::IsBase64Char(&s.get(&int!(0))) && crate::Std::Base64::_default::IsBase64Char(&s.get(&int!(1))) && crate::Std::Base64::_default::IsBase64Char(&s.get(&int!(2))) && crate::Std::Base64::_default::CharToIndex(&s.get(&int!(2))) & 3 as u8 == 0 as u8 && s.get(&int!(3)) == DafnyChar(char::from_u32(61).unwrap())
            }
            /// DafnyStandardLibraries-rs.dfy(5163,3)
            pub fn Decode1Padding(s: &Sequence<DafnyChar>) -> Sequence<u8> {
                let mut d: Sequence<u8> = crate::Std::Base64::_default::DecodeBlock(&seq![crate::Std::Base64::_default::CharToIndex(&s.get(&int!(0))), crate::Std::Base64::_default::CharToIndex(&s.get(&int!(1))), crate::Std::Base64::_default::CharToIndex(&s.get(&int!(2))), 0 as u8]);
                seq![d.get(&int!(0)), d.get(&int!(1))]
            }
            /// DafnyStandardLibraries-rs.dfy(5171,3)
            pub fn Encode1Padding(b: &Sequence<u8>) -> Sequence<DafnyChar> {
                let mut e: Sequence<u8> = crate::Std::Base64::_default::EncodeBlock(&seq![b.get(&int!(0)), b.get(&int!(1)), 0 as u8]);
                seq![crate::Std::Base64::_default::IndexToChar(e.get(&int!(0))), crate::Std::Base64::_default::IndexToChar(e.get(&int!(1))), crate::Std::Base64::_default::IndexToChar(e.get(&int!(2))), DafnyChar(char::from_u32(61).unwrap())]
            }
            /// DafnyStandardLibraries-rs.dfy(5272,3)
            pub fn Is2Padding(s: &Sequence<DafnyChar>) -> bool {
                s.cardinality() == int!(4) && crate::Std::Base64::_default::IsBase64Char(&s.get(&int!(0))) && crate::Std::Base64::_default::IsBase64Char(&s.get(&int!(1))) && crate::Std::Base64::_default::CharToIndex(&s.get(&int!(1))) % 16 as u8 == 0 as u8 && s.get(&int!(2)) == DafnyChar(char::from_u32(61).unwrap()) && s.get(&int!(3)) == DafnyChar(char::from_u32(61).unwrap())
            }
            /// DafnyStandardLibraries-rs.dfy(5282,3)
            pub fn Decode2Padding(s: &Sequence<DafnyChar>) -> Sequence<u8> {
                let mut d: Sequence<u8> = crate::Std::Base64::_default::DecodeBlock(&seq![crate::Std::Base64::_default::CharToIndex(&s.get(&int!(0))), crate::Std::Base64::_default::CharToIndex(&s.get(&int!(1))), 0 as u8, 0 as u8]);
                seq![d.get(&int!(0))]
            }
            /// DafnyStandardLibraries-rs.dfy(5290,3)
            pub fn Encode2Padding(b: &Sequence<u8>) -> Sequence<DafnyChar> {
                let mut e: Sequence<u8> = crate::Std::Base64::_default::EncodeBlock(&seq![b.get(&int!(0)), 0 as u8, 0 as u8]);
                seq![crate::Std::Base64::_default::IndexToChar(e.get(&int!(0))), crate::Std::Base64::_default::IndexToChar(e.get(&int!(1))), DafnyChar(char::from_u32(61).unwrap()), DafnyChar(char::from_u32(61).unwrap())]
            }
            /// DafnyStandardLibraries-rs.dfy(5366,3)
            pub fn IsBase64String(s: &Sequence<DafnyChar>) -> bool {
                let mut finalBlockStart: DafnyInt = s.cardinality() - int!(4);
                euclidian_modulo(s.cardinality(), int!(4)) == int!(0) && (crate::Std::Base64::_default::IsUnpaddedBase64String(s) || crate::Std::Base64::_default::IsUnpaddedBase64String(&s.take(&finalBlockStart)) && (crate::Std::Base64::_default::Is1Padding(&s.drop(&finalBlockStart)) || crate::Std::Base64::_default::Is2Padding(&s.drop(&finalBlockStart))))
            }
            /// DafnyStandardLibraries-rs.dfy(5373,3)
            pub fn DecodeValid(s: &Sequence<DafnyChar>) -> Sequence<u8> {
                if s.clone().to_array().len() == 0 {
                    seq![] as Sequence<u8>
                } else {
                    let mut finalBlockStart: DafnyInt = s.cardinality() - int!(4);
                    let mut prefix: Sequence<DafnyChar> = s.take(&finalBlockStart);
                    let mut suffix: Sequence<DafnyChar> = s.drop(&finalBlockStart);
                    if crate::Std::Base64::_default::Is1Padding(&suffix) {
                        crate::Std::Base64::_default::DecodeUnpadded(&prefix).concat(&crate::Std::Base64::_default::Decode1Padding(&suffix))
                    } else {
                        if crate::Std::Base64::_default::Is2Padding(&suffix) {
                            crate::Std::Base64::_default::DecodeUnpadded(&prefix).concat(&crate::Std::Base64::_default::Decode2Padding(&suffix))
                        } else {
                            crate::Std::Base64::_default::DecodeUnpadded(s)
                        }
                    }
                }
            }
            /// DafnyStandardLibraries-rs.dfy(5421,3)
            pub fn DecodeBV(s: &Sequence<DafnyChar>) -> Rc<Result<Sequence<u8>, Sequence<DafnyChar>>> {
                if crate::Std::Base64::_default::IsBase64String(s) {
                    Rc::new(Result::Success::<Sequence<u8>, Sequence<DafnyChar>> {
                            value: crate::Std::Base64::_default::DecodeValid(s)
                        })
                } else {
                    Rc::new(Result::Failure::<Sequence<u8>, Sequence<DafnyChar>> {
                            error: string_of("The encoding is malformed")
                        })
                }
            }
            /// DafnyStandardLibraries-rs.dfy(5460,3)
            pub fn EncodeBV(b: &Sequence<u8>) -> Sequence<DafnyChar> {
                if euclidian_modulo(b.cardinality(), int!(3)) == int!(0) {
                    crate::Std::Base64::_default::EncodeUnpadded(b)
                } else {
                    if euclidian_modulo(b.cardinality(), int!(3)) == int!(1) {
                        let mut s1: Sequence<DafnyChar> = crate::Std::Base64::_default::EncodeUnpadded(&b.take(&(b.cardinality() - int!(1))));
                        let mut s2: Sequence<DafnyChar> = crate::Std::Base64::_default::Encode2Padding(&b.drop(&(b.cardinality() - int!(1))));
                        s1.concat(&s2)
                    } else {
                        let mut s1: Sequence<DafnyChar> = crate::Std::Base64::_default::EncodeUnpadded(&b.take(&(b.cardinality() - int!(2))));
                        let mut s2: Sequence<DafnyChar> = crate::Std::Base64::_default::Encode1Padding(&b.drop(&(b.cardinality() - int!(2))));
                        s1.concat(&s2)
                    }
                }
            }
            /// DafnyStandardLibraries-rs.dfy(6000,3)
            pub fn UInt8sToBVs(u: &Sequence<u8>) -> Sequence<u8> {
                {
                    let _initializer = {
                            let u: Sequence<u8> = u.clone();
                            {
                                let mut u = u.clone();
                                Rc::new(move |i: &DafnyInt| -> u8{
            u.get(i) as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        };
                    integer_range(Zero::zero(), u.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(6007,3)
            pub fn BVsToUInt8s(b: &Sequence<u8>) -> Sequence<u8> {
                {
                    let _initializer = {
                            let b: Sequence<u8> = b.clone();
                            {
                                let mut b = b.clone();
                                Rc::new(move |i: &DafnyInt| -> u8{
            b.get(i) as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        };
                    integer_range(Zero::zero(), b.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(6032,3)
            pub fn Encode(u: &Sequence<u8>) -> Sequence<DafnyChar> {
                crate::Std::Base64::_default::EncodeBV(&crate::Std::Base64::_default::UInt8sToBVs(u))
            }
            /// DafnyStandardLibraries-rs.dfy(6037,3)
            pub fn Decode(s: &Sequence<DafnyChar>) -> Rc<Result<Sequence<u8>, Sequence<DafnyChar>>> {
                if crate::Std::Base64::_default::IsBase64String(s) {
                    let mut b: Sequence<u8> = crate::Std::Base64::_default::DecodeValid(s);
                    Rc::new(Result::Success::<Sequence<u8>, Sequence<DafnyChar>> {
                            value: crate::Std::Base64::_default::BVsToUInt8s(&b)
                        })
                } else {
                    Rc::new(Result::Failure::<Sequence<u8>, Sequence<DafnyChar>> {
                            error: string_of("The encoding is malformed")
                        })
                }
            }
        }
    }

    /// DafnyStandardLibraries-rs.dfy(6102,1)
    pub mod BoundedInts {
        pub use ::dafny_runtime::DafnyInt;
        pub use ::dafny_runtime::int;
        pub use ::dafny_runtime::truncate;
        pub use ::std::cmp::PartialEq;
        pub use ::std::cmp::Eq;
        pub use ::std::hash::Hash;
        pub use ::std::hash::Hasher;
        pub use ::std::default::Default;
        pub use ::dafny_runtime::DafnyPrint;
        pub use ::std::fmt::Formatter;
        pub use ::std::fmt::Result;
        pub use ::std::ops::Deref;
        pub use ::std::mem::transmute;
        pub use ::std::ops::Add;
        pub use ::std::ops::Sub;
        pub use ::std::ops::Mul;
        pub use ::std::ops::Div;
        pub use ::std::cmp::PartialOrd;
        pub use ::std::option::Option;
        pub use ::std::cmp::Ordering;

        pub struct _default {}

        impl _default {
            /// DafnyStandardLibraries-rs.dfy(6109,3)
            pub fn TWO_TO_THE_8() -> DafnyInt {
                int!(256)
            }
            /// DafnyStandardLibraries-rs.dfy(6124,3)
            pub fn UINT8_MAX() -> u8 {
                truncate!(int!(255), u8)
            }
            /// DafnyStandardLibraries-rs.dfy(6111,3)
            pub fn TWO_TO_THE_16() -> DafnyInt {
                int!(b"65536")
            }
            /// DafnyStandardLibraries-rs.dfy(6125,3)
            pub fn UINT16_MAX() -> u16 {
                truncate!(int!(b"65535"), u16)
            }
            /// DafnyStandardLibraries-rs.dfy(6114,3)
            pub fn TWO_TO_THE_32() -> DafnyInt {
                int!(b"4294967296")
            }
            /// DafnyStandardLibraries-rs.dfy(6126,3)
            pub fn UINT32_MAX() -> u32 {
                truncate!(int!(b"4294967295"), u32)
            }
            /// DafnyStandardLibraries-rs.dfy(6119,3)
            pub fn TWO_TO_THE_64() -> DafnyInt {
                int!(b"18446744073709551616")
            }
            /// DafnyStandardLibraries-rs.dfy(6127,3)
            pub fn UINT64_MAX() -> u64 {
                truncate!(int!(b"18446744073709551615"), u64)
            }
            /// DafnyStandardLibraries-rs.dfy(6108,3)
            pub fn TWO_TO_THE_7() -> DafnyInt {
                int!(128)
            }
            /// DafnyStandardLibraries-rs.dfy(6128,3)
            pub fn INT8_MIN() -> i8 {
                truncate!(int!(-128), i8)
            }
            /// DafnyStandardLibraries-rs.dfy(6129,3)
            pub fn INT8_MAX() -> i8 {
                truncate!(int!(127), i8)
            }
            /// DafnyStandardLibraries-rs.dfy(6110,3)
            pub fn TWO_TO_THE_15() -> DafnyInt {
                int!(b"32768")
            }
            /// DafnyStandardLibraries-rs.dfy(6130,3)
            pub fn INT16_MIN() -> i16 {
                truncate!(int!(b"-32768"), i16)
            }
            /// DafnyStandardLibraries-rs.dfy(6131,3)
            pub fn INT16_MAX() -> i16 {
                truncate!(int!(b"32767"), i16)
            }
            /// DafnyStandardLibraries-rs.dfy(6113,3)
            pub fn TWO_TO_THE_31() -> DafnyInt {
                int!(b"2147483648")
            }
            /// DafnyStandardLibraries-rs.dfy(6132,3)
            pub fn INT32_MIN() -> i32 {
                truncate!(int!(b"-2147483648"), i32)
            }
            /// DafnyStandardLibraries-rs.dfy(6133,3)
            pub fn INT32_MAX() -> i32 {
                truncate!(int!(b"2147483647"), i32)
            }
            /// DafnyStandardLibraries-rs.dfy(6118,3)
            pub fn TWO_TO_THE_63() -> DafnyInt {
                int!(b"9223372036854775808")
            }
            /// DafnyStandardLibraries-rs.dfy(6134,3)
            pub fn INT64_MIN() -> i64 {
                truncate!(int!(b"-9223372036854775808"), i64)
            }
            /// DafnyStandardLibraries-rs.dfy(6135,3)
            pub fn INT64_MAX() -> i64 {
                truncate!(int!(b"9223372036854775807"), i64)
            }
            /// DafnyStandardLibraries-rs.dfy(6136,3)
            pub fn NAT8_MAX() -> u8 {
                truncate!(int!(127), u8)
            }
            /// DafnyStandardLibraries-rs.dfy(6137,3)
            pub fn NAT16_MAX() -> u16 {
                truncate!(int!(b"32767"), u16)
            }
            /// DafnyStandardLibraries-rs.dfy(6138,3)
            pub fn NAT32_MAX() -> u32 {
                truncate!(int!(b"2147483647"), u32)
            }
            /// DafnyStandardLibraries-rs.dfy(6139,3)
            pub fn NAT64_MAX() -> u64 {
                truncate!(int!(b"9223372036854775807"), u64)
            }
            /// DafnyStandardLibraries-rs.dfy(6121,3)
            pub fn TWO_TO_THE_128() -> DafnyInt {
                int!(b"340282366920938463463374607431768211456")
            }
            /// DafnyStandardLibraries-rs.dfy(6120,3)
            pub fn TWO_TO_THE_127() -> DafnyInt {
                int!(b"170141183460469231731687303715884105728")
            }
            /// DafnyStandardLibraries-rs.dfy(6103,3)
            pub fn TWO_TO_THE_0() -> DafnyInt {
                int!(1)
            }
            /// DafnyStandardLibraries-rs.dfy(6104,3)
            pub fn TWO_TO_THE_1() -> DafnyInt {
                int!(2)
            }
            /// DafnyStandardLibraries-rs.dfy(6105,3)
            pub fn TWO_TO_THE_2() -> DafnyInt {
                int!(4)
            }
            /// DafnyStandardLibraries-rs.dfy(6106,3)
            pub fn TWO_TO_THE_4() -> DafnyInt {
                int!(16)
            }
            /// DafnyStandardLibraries-rs.dfy(6107,3)
            pub fn TWO_TO_THE_5() -> DafnyInt {
                int!(32)
            }
            /// DafnyStandardLibraries-rs.dfy(6112,3)
            pub fn TWO_TO_THE_24() -> DafnyInt {
                int!(b"16777216")
            }
            /// DafnyStandardLibraries-rs.dfy(6115,3)
            pub fn TWO_TO_THE_40() -> DafnyInt {
                int!(b"1099511627776")
            }
            /// DafnyStandardLibraries-rs.dfy(6116,3)
            pub fn TWO_TO_THE_48() -> DafnyInt {
                int!(b"281474976710656")
            }
            /// DafnyStandardLibraries-rs.dfy(6117,3)
            pub fn TWO_TO_THE_56() -> DafnyInt {
                int!(b"72057594037927936")
            }
            /// DafnyStandardLibraries-rs.dfy(6122,3)
            pub fn TWO_TO_THE_256() -> DafnyInt {
                int!(b"115792089237316195423570985008687907853269984665640564039457584007913129639936")
            }
            /// DafnyStandardLibraries-rs.dfy(6123,3)
            pub fn TWO_TO_THE_512() -> DafnyInt {
                int!(b"13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096")
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6141,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct uint8(pub u8);

        impl PartialEq
            for uint8 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for uint8 {}

        impl Hash
            for uint8 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl uint8 {
            /// Constraint check
            pub fn is(_source: u8) -> bool {
                return true;
            }
        }

        impl Default
            for uint8 {
            /// An element of uint8
            fn default() -> Self {
                uint8(Default::default())
            }
        }

        impl DafnyPrint
            for uint8 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for uint8 {
            type Target = u8;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl uint8 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u8) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for uint8 {
            type Output = uint8;
            fn add(self, other: Self) -> Self {
                uint8(self.0 + other.0)
            }
        }

        impl Sub
            for uint8 {
            type Output = uint8;
            fn sub(self, other: Self) -> Self {
                uint8(self.0 - other.0)
            }
        }

        impl Mul
            for uint8 {
            type Output = uint8;
            fn mul(self, other: Self) -> Self {
                uint8(self.0 * other.0)
            }
        }

        impl Div
            for uint8 {
            type Output = uint8;
            fn div(self, other: Self) -> Self {
                uint8(self.0 / other.0)
            }
        }

        impl PartialOrd
            for uint8 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6144,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct uint16(pub u16);

        impl PartialEq
            for uint16 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for uint16 {}

        impl Hash
            for uint16 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl uint16 {
            /// Constraint check
            pub fn is(_source: u16) -> bool {
                return true;
            }
        }

        impl Default
            for uint16 {
            /// An element of uint16
            fn default() -> Self {
                uint16(Default::default())
            }
        }

        impl DafnyPrint
            for uint16 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for uint16 {
            type Target = u16;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl uint16 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u16) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for uint16 {
            type Output = uint16;
            fn add(self, other: Self) -> Self {
                uint16(self.0 + other.0)
            }
        }

        impl Sub
            for uint16 {
            type Output = uint16;
            fn sub(self, other: Self) -> Self {
                uint16(self.0 - other.0)
            }
        }

        impl Mul
            for uint16 {
            type Output = uint16;
            fn mul(self, other: Self) -> Self {
                uint16(self.0 * other.0)
            }
        }

        impl Div
            for uint16 {
            type Output = uint16;
            fn div(self, other: Self) -> Self {
                uint16(self.0 / other.0)
            }
        }

        impl PartialOrd
            for uint16 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6147,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct uint32(pub u32);

        impl PartialEq
            for uint32 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for uint32 {}

        impl Hash
            for uint32 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl uint32 {
            /// Constraint check
            pub fn is(_source: u32) -> bool {
                return true;
            }
        }

        impl Default
            for uint32 {
            /// An element of uint32
            fn default() -> Self {
                uint32(Default::default())
            }
        }

        impl DafnyPrint
            for uint32 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for uint32 {
            type Target = u32;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl uint32 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u32) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for uint32 {
            type Output = uint32;
            fn add(self, other: Self) -> Self {
                uint32(self.0 + other.0)
            }
        }

        impl Sub
            for uint32 {
            type Output = uint32;
            fn sub(self, other: Self) -> Self {
                uint32(self.0 - other.0)
            }
        }

        impl Mul
            for uint32 {
            type Output = uint32;
            fn mul(self, other: Self) -> Self {
                uint32(self.0 * other.0)
            }
        }

        impl Div
            for uint32 {
            type Output = uint32;
            fn div(self, other: Self) -> Self {
                uint32(self.0 / other.0)
            }
        }

        impl PartialOrd
            for uint32 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6150,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct uint64(pub u64);

        impl PartialEq
            for uint64 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for uint64 {}

        impl Hash
            for uint64 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl uint64 {
            /// Constraint check
            pub fn is(_source: u64) -> bool {
                return true;
            }
        }

        impl Default
            for uint64 {
            /// An element of uint64
            fn default() -> Self {
                uint64(Default::default())
            }
        }

        impl DafnyPrint
            for uint64 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for uint64 {
            type Target = u64;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl uint64 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u64) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for uint64 {
            type Output = uint64;
            fn add(self, other: Self) -> Self {
                uint64(self.0 + other.0)
            }
        }

        impl Sub
            for uint64 {
            type Output = uint64;
            fn sub(self, other: Self) -> Self {
                uint64(self.0 - other.0)
            }
        }

        impl Mul
            for uint64 {
            type Output = uint64;
            fn mul(self, other: Self) -> Self {
                uint64(self.0 * other.0)
            }
        }

        impl Div
            for uint64 {
            type Output = uint64;
            fn div(self, other: Self) -> Self {
                uint64(self.0 / other.0)
            }
        }

        impl PartialOrd
            for uint64 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6153,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct uint128(pub u128);

        impl PartialEq
            for uint128 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for uint128 {}

        impl Hash
            for uint128 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl uint128 {
            /// Constraint check
            pub fn is(_source: u128) -> bool {
                return true;
            }
        }

        impl Default
            for uint128 {
            /// An element of uint128
            fn default() -> Self {
                uint128(Default::default())
            }
        }

        impl DafnyPrint
            for uint128 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for uint128 {
            type Target = u128;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl uint128 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u128) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for uint128 {
            type Output = uint128;
            fn add(self, other: Self) -> Self {
                uint128(self.0 + other.0)
            }
        }

        impl Sub
            for uint128 {
            type Output = uint128;
            fn sub(self, other: Self) -> Self {
                uint128(self.0 - other.0)
            }
        }

        impl Mul
            for uint128 {
            type Output = uint128;
            fn mul(self, other: Self) -> Self {
                uint128(self.0 * other.0)
            }
        }

        impl Div
            for uint128 {
            type Output = uint128;
            fn div(self, other: Self) -> Self {
                uint128(self.0 / other.0)
            }
        }

        impl PartialOrd
            for uint128 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6156,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct int8(pub i8);

        impl PartialEq
            for int8 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for int8 {}

        impl Hash
            for int8 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl int8 {
            /// Constraint check
            pub fn is(_source: i8) -> bool {
                return true;
            }
        }

        impl Default
            for int8 {
            /// An element of int8
            fn default() -> Self {
                int8(Default::default())
            }
        }

        impl DafnyPrint
            for int8 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for int8 {
            type Target = i8;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl int8 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &i8) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for int8 {
            type Output = int8;
            fn add(self, other: Self) -> Self {
                int8(self.0 + other.0)
            }
        }

        impl Sub
            for int8 {
            type Output = int8;
            fn sub(self, other: Self) -> Self {
                int8(self.0 - other.0)
            }
        }

        impl Mul
            for int8 {
            type Output = int8;
            fn mul(self, other: Self) -> Self {
                int8(self.0 * other.0)
            }
        }

        impl Div
            for int8 {
            type Output = int8;
            fn div(self, other: Self) -> Self {
                int8(self.0 / other.0)
            }
        }

        impl PartialOrd
            for int8 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6159,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct int16(pub i16);

        impl PartialEq
            for int16 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for int16 {}

        impl Hash
            for int16 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl int16 {
            /// Constraint check
            pub fn is(_source: i16) -> bool {
                return true;
            }
        }

        impl Default
            for int16 {
            /// An element of int16
            fn default() -> Self {
                int16(Default::default())
            }
        }

        impl DafnyPrint
            for int16 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for int16 {
            type Target = i16;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl int16 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &i16) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for int16 {
            type Output = int16;
            fn add(self, other: Self) -> Self {
                int16(self.0 + other.0)
            }
        }

        impl Sub
            for int16 {
            type Output = int16;
            fn sub(self, other: Self) -> Self {
                int16(self.0 - other.0)
            }
        }

        impl Mul
            for int16 {
            type Output = int16;
            fn mul(self, other: Self) -> Self {
                int16(self.0 * other.0)
            }
        }

        impl Div
            for int16 {
            type Output = int16;
            fn div(self, other: Self) -> Self {
                int16(self.0 / other.0)
            }
        }

        impl PartialOrd
            for int16 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6162,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct int32(pub i32);

        impl PartialEq
            for int32 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for int32 {}

        impl Hash
            for int32 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl int32 {
            /// Constraint check
            pub fn is(_source: i32) -> bool {
                return true;
            }
        }

        impl Default
            for int32 {
            /// An element of int32
            fn default() -> Self {
                int32(Default::default())
            }
        }

        impl DafnyPrint
            for int32 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for int32 {
            type Target = i32;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl int32 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &i32) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for int32 {
            type Output = int32;
            fn add(self, other: Self) -> Self {
                int32(self.0 + other.0)
            }
        }

        impl Sub
            for int32 {
            type Output = int32;
            fn sub(self, other: Self) -> Self {
                int32(self.0 - other.0)
            }
        }

        impl Mul
            for int32 {
            type Output = int32;
            fn mul(self, other: Self) -> Self {
                int32(self.0 * other.0)
            }
        }

        impl Div
            for int32 {
            type Output = int32;
            fn div(self, other: Self) -> Self {
                int32(self.0 / other.0)
            }
        }

        impl PartialOrd
            for int32 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6165,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct int64(pub i64);

        impl PartialEq
            for int64 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for int64 {}

        impl Hash
            for int64 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl int64 {
            /// Constraint check
            pub fn is(_source: i64) -> bool {
                return true;
            }
        }

        impl Default
            for int64 {
            /// An element of int64
            fn default() -> Self {
                int64(Default::default())
            }
        }

        impl DafnyPrint
            for int64 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for int64 {
            type Target = i64;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl int64 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &i64) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for int64 {
            type Output = int64;
            fn add(self, other: Self) -> Self {
                int64(self.0 + other.0)
            }
        }

        impl Sub
            for int64 {
            type Output = int64;
            fn sub(self, other: Self) -> Self {
                int64(self.0 - other.0)
            }
        }

        impl Mul
            for int64 {
            type Output = int64;
            fn mul(self, other: Self) -> Self {
                int64(self.0 * other.0)
            }
        }

        impl Div
            for int64 {
            type Output = int64;
            fn div(self, other: Self) -> Self {
                int64(self.0 / other.0)
            }
        }

        impl PartialOrd
            for int64 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6168,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct int128(pub i128);

        impl PartialEq
            for int128 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for int128 {}

        impl Hash
            for int128 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl int128 {
            /// Constraint check
            pub fn is(_source: i128) -> bool {
                return true;
            }
        }

        impl Default
            for int128 {
            /// An element of int128
            fn default() -> Self {
                int128(Default::default())
            }
        }

        impl DafnyPrint
            for int128 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for int128 {
            type Target = i128;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl int128 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &i128) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for int128 {
            type Output = int128;
            fn add(self, other: Self) -> Self {
                int128(self.0 + other.0)
            }
        }

        impl Sub
            for int128 {
            type Output = int128;
            fn sub(self, other: Self) -> Self {
                int128(self.0 - other.0)
            }
        }

        impl Mul
            for int128 {
            type Output = int128;
            fn mul(self, other: Self) -> Self {
                int128(self.0 * other.0)
            }
        }

        impl Div
            for int128 {
            type Output = int128;
            fn div(self, other: Self) -> Self {
                int128(self.0 / other.0)
            }
        }

        impl PartialOrd
            for int128 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6171,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct nat8(pub u8);

        impl PartialEq
            for nat8 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for nat8 {}

        impl Hash
            for nat8 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl nat8 {
            /// Constraint check
            pub fn is(_source: u8) -> bool {
                let mut x: DafnyInt = int!(_source.clone());
                return !(x.clone() < int!(0)) && x.clone() < crate::Std::BoundedInts::_default::TWO_TO_THE_7();
            }
        }

        impl Default
            for nat8 {
            /// An element of nat8
            fn default() -> Self {
                nat8(Default::default())
            }
        }

        impl DafnyPrint
            for nat8 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for nat8 {
            type Target = u8;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl nat8 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u8) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for nat8 {
            type Output = nat8;
            fn add(self, other: Self) -> Self {
                nat8(self.0 + other.0)
            }
        }

        impl Sub
            for nat8 {
            type Output = nat8;
            fn sub(self, other: Self) -> Self {
                nat8(self.0 - other.0)
            }
        }

        impl Mul
            for nat8 {
            type Output = nat8;
            fn mul(self, other: Self) -> Self {
                nat8(self.0 * other.0)
            }
        }

        impl Div
            for nat8 {
            type Output = nat8;
            fn div(self, other: Self) -> Self {
                nat8(self.0 / other.0)
            }
        }

        impl PartialOrd
            for nat8 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6174,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct nat16(pub u16);

        impl PartialEq
            for nat16 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for nat16 {}

        impl Hash
            for nat16 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl nat16 {
            /// Constraint check
            pub fn is(_source: u16) -> bool {
                let mut x: DafnyInt = int!(_source.clone());
                return !(x.clone() < int!(0)) && x.clone() < crate::Std::BoundedInts::_default::TWO_TO_THE_15();
            }
        }

        impl Default
            for nat16 {
            /// An element of nat16
            fn default() -> Self {
                nat16(Default::default())
            }
        }

        impl DafnyPrint
            for nat16 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for nat16 {
            type Target = u16;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl nat16 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u16) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for nat16 {
            type Output = nat16;
            fn add(self, other: Self) -> Self {
                nat16(self.0 + other.0)
            }
        }

        impl Sub
            for nat16 {
            type Output = nat16;
            fn sub(self, other: Self) -> Self {
                nat16(self.0 - other.0)
            }
        }

        impl Mul
            for nat16 {
            type Output = nat16;
            fn mul(self, other: Self) -> Self {
                nat16(self.0 * other.0)
            }
        }

        impl Div
            for nat16 {
            type Output = nat16;
            fn div(self, other: Self) -> Self {
                nat16(self.0 / other.0)
            }
        }

        impl PartialOrd
            for nat16 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6177,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct nat32(pub u32);

        impl PartialEq
            for nat32 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for nat32 {}

        impl Hash
            for nat32 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl nat32 {
            /// Constraint check
            pub fn is(_source: u32) -> bool {
                let mut x: DafnyInt = int!(_source.clone());
                return !(x.clone() < int!(0)) && x.clone() < crate::Std::BoundedInts::_default::TWO_TO_THE_31();
            }
        }

        impl Default
            for nat32 {
            /// An element of nat32
            fn default() -> Self {
                nat32(Default::default())
            }
        }

        impl DafnyPrint
            for nat32 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for nat32 {
            type Target = u32;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl nat32 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u32) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for nat32 {
            type Output = nat32;
            fn add(self, other: Self) -> Self {
                nat32(self.0 + other.0)
            }
        }

        impl Sub
            for nat32 {
            type Output = nat32;
            fn sub(self, other: Self) -> Self {
                nat32(self.0 - other.0)
            }
        }

        impl Mul
            for nat32 {
            type Output = nat32;
            fn mul(self, other: Self) -> Self {
                nat32(self.0 * other.0)
            }
        }

        impl Div
            for nat32 {
            type Output = nat32;
            fn div(self, other: Self) -> Self {
                nat32(self.0 / other.0)
            }
        }

        impl PartialOrd
            for nat32 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6180,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct nat64(pub u64);

        impl PartialEq
            for nat64 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for nat64 {}

        impl Hash
            for nat64 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl nat64 {
            /// Constraint check
            pub fn is(_source: u64) -> bool {
                let mut x: DafnyInt = int!(_source.clone());
                return !(x.clone() < int!(0)) && x.clone() < crate::Std::BoundedInts::_default::TWO_TO_THE_63();
            }
        }

        impl Default
            for nat64 {
            /// An element of nat64
            fn default() -> Self {
                nat64(Default::default())
            }
        }

        impl DafnyPrint
            for nat64 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for nat64 {
            type Target = u64;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl nat64 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u64) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for nat64 {
            type Output = nat64;
            fn add(self, other: Self) -> Self {
                nat64(self.0 + other.0)
            }
        }

        impl Sub
            for nat64 {
            type Output = nat64;
            fn sub(self, other: Self) -> Self {
                nat64(self.0 - other.0)
            }
        }

        impl Mul
            for nat64 {
            type Output = nat64;
            fn mul(self, other: Self) -> Self {
                nat64(self.0 * other.0)
            }
        }

        impl Div
            for nat64 {
            type Output = nat64;
            fn div(self, other: Self) -> Self {
                nat64(self.0 / other.0)
            }
        }

        impl PartialOrd
            for nat64 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6183,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct nat128(pub u128);

        impl PartialEq
            for nat128 {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for nat128 {}

        impl Hash
            for nat128 {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl nat128 {
            /// Constraint check
            pub fn is(_source: u128) -> bool {
                let mut x: DafnyInt = int!(_source.clone());
                return !(x.clone() < int!(0)) && x.clone() < crate::Std::BoundedInts::_default::TWO_TO_THE_127();
            }
        }

        impl Default
            for nat128 {
            /// An element of nat128
            fn default() -> Self {
                nat128(Default::default())
            }
        }

        impl DafnyPrint
            for nat128 {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for nat128 {
            type Target = u128;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl nat128 {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &u128) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for nat128 {
            type Output = nat128;
            fn add(self, other: Self) -> Self {
                nat128(self.0 + other.0)
            }
        }

        impl Sub
            for nat128 {
            type Output = nat128;
            fn sub(self, other: Self) -> Self {
                nat128(self.0 - other.0)
            }
        }

        impl Mul
            for nat128 {
            type Output = nat128;
            fn mul(self, other: Self) -> Self {
                nat128(self.0 * other.0)
            }
        }

        impl Div
            for nat128 {
            type Output = nat128;
            fn div(self, other: Self) -> Self {
                nat128(self.0 / other.0)
            }
        }

        impl PartialOrd
            for nat128 {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6190,3)
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct opt_byte(pub i16);

        impl PartialEq
            for opt_byte {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq
            for opt_byte {}

        impl Hash
            for opt_byte {
            fn hash<_H: Hasher>(&self, _state: &mut _H) {
                Hash::hash(&self.0, _state)
            }
        }

        impl opt_byte {
            /// Constraint check
            pub fn is(_source: i16) -> bool {
                let mut c: DafnyInt = int!(_source.clone());
                return !(c.clone() < int!(-1)) && c.clone() < crate::Std::BoundedInts::_default::TWO_TO_THE_8();
            }
        }

        impl Default
            for opt_byte {
            /// An element of opt_byte
            fn default() -> Self {
                opt_byte(Default::default())
            }
        }

        impl DafnyPrint
            for opt_byte {
            /// For Dafny print statements
            fn fmt_print(&self, _formatter: &mut Formatter, in_seq: bool) -> Result {
                DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl Deref
            for opt_byte {
            type Target = i16;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl opt_byte {
            /// SAFETY: The newtype is marked as transparent
            pub fn _from_ref(o: &i16) -> &Self {
                unsafe {
                    transmute(o)
                }
            }
        }

        impl Add
            for opt_byte {
            type Output = opt_byte;
            fn add(self, other: Self) -> Self {
                opt_byte(self.0 + other.0)
            }
        }

        impl Sub
            for opt_byte {
            type Output = opt_byte;
            fn sub(self, other: Self) -> Self {
                opt_byte(self.0 - other.0)
            }
        }

        impl Mul
            for opt_byte {
            type Output = opt_byte;
            fn mul(self, other: Self) -> Self {
                opt_byte(self.0 * other.0)
            }
        }

        impl Div
            for opt_byte {
            type Output = opt_byte;
            fn div(self, other: Self) -> Self {
                opt_byte(self.0 / other.0)
            }
        }

        impl PartialOrd
            for opt_byte {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&self.0, &other.0)
            }
        }
    }

    /// DafnyStandardLibraries-rs.dfy(6227,1)
    pub mod Collections {
        /// DafnyStandardLibraries-rs.dfy(6194,1)
        pub mod Array {
            pub use ::dafny_runtime::DafnyType;
            pub use ::dafny_runtime::Object;
            pub use ::std::rc::Rc;
            pub use crate::Std::Wrappers::Option;
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::MaybePlacebo;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::rd;
            pub use ::dafny_runtime::euclidian_division;
            pub use ::dafny_runtime::DafnyUsize;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(6195,3)
                pub fn BinarySearch<_T: DafnyType>(a: &Object<[_T]>, key: &_T, less: &Rc<dyn ::std::ops::Fn(&_T, &_T) -> bool>) -> Rc<Option<nat>> {
                    let mut r = MaybePlacebo::<Rc<Option<nat>>>::new();
                    let mut lo: DafnyInt;
                    let mut hi: nat;
                    let mut _rhs0: DafnyInt = int!(0);
                    let mut _rhs1: DafnyInt = int!(rd!(a.clone()).len());
                    lo = _rhs0.clone();
                    hi = _rhs1.clone();
                    while lo.clone() < hi.clone() {
                        let mut mid: DafnyInt = euclidian_division(lo.clone() + hi.clone(), int!(2));
                        if less(key, &rd!(a)[DafnyUsize::into_usize(mid.clone())].clone()) {
                            hi = mid.clone();
                        } else {
                            if less(&rd!(a)[DafnyUsize::into_usize(mid.clone())].clone(), key) {
                                lo = mid.clone() + int!(1);
                            } else {
                                r = MaybePlacebo::from(Rc::new(Option::Some::<DafnyInt> {
                                                value: mid.clone()
                                            }));
                                return r.read();
                            }
                        }
                    };
                    r = MaybePlacebo::from(Rc::new(Option::None::<nat> {}));
                    return r.read();
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6230,1)
        pub mod Imap {
            pub use ::dafny_runtime::DafnyTypeEq;
            pub use ::dafny_runtime::DafnyType;
            pub use ::dafny_runtime::Map;
            pub use ::std::rc::Rc;
            pub use crate::Std::Wrappers::Option;
            pub use ::dafny_runtime::upcast_id;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(6231,3)
                pub fn Get<_X: DafnyTypeEq, _Y: DafnyType>(m: &Map<_X, _Y>, x: &_X) -> Rc<Option<_Y>> {
                    if m.contains(x) {
                        Rc::new(Option::Some::<_Y> {
                                value: m.get(&upcast_id::<_X>()(x.clone()))
                            })
                    } else {
                        Rc::new(Option::None::<_Y> {})
                    }
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6327,1)
        pub mod Iset {
            
        }

        /// DafnyStandardLibraries-rs.dfy(6358,1)
        pub mod Map {
            pub use ::dafny_runtime::DafnyTypeEq;
            pub use ::dafny_runtime::DafnyType;
            pub use ::dafny_runtime::Map;
            pub use ::std::rc::Rc;
            pub use crate::Std::Wrappers::Option;
            pub use ::dafny_runtime::MapBuilder;
            pub use ::dafny_runtime::Set;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(6359,3)
                pub fn Get<_X: DafnyTypeEq, _Y: DafnyType>(m: &Map<_X, _Y>, x: &_X) -> Rc<Option<_Y>> {
                    if m.contains(x) {
                        Rc::new(Option::Some::<_Y> {
                                value: m.get(x)
                            })
                    } else {
                        Rc::new(Option::None::<_Y> {})
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6367,3)
                pub fn ToImap<_X: DafnyTypeEq, _Y: DafnyType>(m: &Map<_X, _Y>) -> Map<_X, _Y> {
                    (&({
                        let mut m = m.clone();
                        Rc::new(move || -> Map<_X, _Y>{
            let mut _coll0: MapBuilder<_X, _Y> = MapBuilder::<_X, _Y>::new();
            for __compr_0 in (&m).keys().iter().cloned() {
                let mut x: _X = __compr_0.clone();
                if m.contains(&x) {
                    _coll0.add(&x, &m.get(&x))
                }
            }
            _coll0.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
                    }))()
                }
                /// DafnyStandardLibraries-rs.dfy(6374,3)
                pub fn RemoveKeys<_X: DafnyTypeEq, _Y: DafnyType>(m: &Map<_X, _Y>, xs: &Set<_X>) -> Map<_X, _Y> {
                    m.subtract(xs)
                }
                /// DafnyStandardLibraries-rs.dfy(6382,3)
                pub fn Remove<_X: DafnyTypeEq, _Y: DafnyType>(m: &Map<_X, _Y>, x: &_X) -> Map<_X, _Y> {
                    let mut _m_k: Map<_X, _Y> = (&({
                            let mut m = m.clone();
                            let mut x = x.clone();
                            Rc::new(move || -> Map<_X, _Y>{
            let mut _coll0: MapBuilder<_X, _Y> = MapBuilder::<_X, _Y>::new();
            for __compr_0 in (&m).keys().iter().cloned() {
                let mut _x_k: _X = __compr_0.clone();
                if m.contains(&_x_k) && !(_x_k.clone() == x.clone()) {
                    _coll0.add(&_x_k, &m.get(&_x_k))
                }
            }
            _coll0.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
                        }))();
                    _m_k.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(6393,3)
                pub fn Restrict<_X: DafnyTypeEq, _Y: DafnyType>(m: &Map<_X, _Y>, xs: &Set<_X>) -> Map<_X, _Y> {
                    (&({
                        let mut m = m.clone();
                        let mut xs = xs.clone();
                        Rc::new(move || -> Map<_X, _Y>{
            let mut _coll0: MapBuilder<_X, _Y> = MapBuilder::<_X, _Y>::new();
            for __compr_0 in (&xs).iter().cloned() {
                let mut x: _X = __compr_0.clone();
                if xs.contains(&x) && m.contains(&x) {
                    _coll0.add(&x, &m.get(&x))
                }
            }
            _coll0.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
                    }))()
                }
                /// DafnyStandardLibraries-rs.dfy(6412,3)
                pub fn Union<_X: DafnyTypeEq, _Y: DafnyType>(m: &Map<_X, _Y>, _m_k: &Map<_X, _Y>) -> Map<_X, _Y> {
                    m.merge(_m_k)
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(6474,1)
        pub mod Multiset {
            
        }

        /// DafnyStandardLibraries-rs.dfy(6494,1)
        pub mod Seq {
            pub use ::dafny_runtime::DafnyType;
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::Object;
            pub use ::dafny_runtime::MaybePlacebo;
            pub use ::std::rc::Rc;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::std::mem::MaybeUninit;
            pub use ::dafny_runtime::array;
            pub use ::dafny_runtime::DafnyUsize;
            pub use ::dafny_runtime::integer_range;
            pub use ::dafny_runtime::truncate;
            pub use ::dafny_runtime::rd;
            pub use ::dafny_runtime::DafnyTypeEq;
            pub use ::dafny_runtime::Set;
            pub use ::dafny_runtime::SetBuilder;
            pub use ::dafny_runtime::_System::nat;
            pub use crate::Std::Wrappers::Option;
            pub use crate::Std::Wrappers::Option::Some;
            pub use ::dafny_runtime::seq;
            pub use ::dafny_runtime::euclidian_division;
            pub use ::std::fmt::Debug;
            pub use ::std::fmt::Formatter;
            pub use ::dafny_runtime::DafnyPrint;
            pub use ::std::cmp::Eq;
            pub use ::std::hash::Hash;
            pub use ::std::cmp::PartialEq;
            pub use ::std::hash::Hasher;
            pub use ::std::convert::AsRef;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(6495,3)
                pub fn First<_T: DafnyType>(xs: &Sequence<_T>) -> _T {
                    xs.get(&int!(0))
                }
                /// DafnyStandardLibraries-rs.dfy(6501,3)
                pub fn DropFirst<_T: DafnyType>(xs: &Sequence<_T>) -> Sequence<_T> {
                    xs.drop(&int!(1))
                }
                /// DafnyStandardLibraries-rs.dfy(6507,3)
                pub fn Last<_T: DafnyType>(xs: &Sequence<_T>) -> _T {
                    xs.get(&(xs.cardinality() - int!(1)))
                }
                /// DafnyStandardLibraries-rs.dfy(6513,3)
                pub fn DropLast<_T: DafnyType>(xs: &Sequence<_T>) -> Sequence<_T> {
                    xs.take(&(xs.cardinality() - int!(1)))
                }
                /// DafnyStandardLibraries-rs.dfy(6593,3)
                pub fn ToArray<_T: DafnyType>(xs: &Sequence<_T>) -> Object<[_T]> {
                    let mut a = MaybePlacebo::<Object<[_T]>>::new();
                    let mut _init0: Rc<dyn ::std::ops::Fn(&DafnyInt) -> _T> = {
                            let xs: Sequence<_T> = xs.clone();
                            {
                                let mut xs = xs.clone();
                                Rc::new(move |i: &DafnyInt| -> _T{
            xs.get(i)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        };
                    let mut _nw0: Object<[MaybeUninit<_T>]> = array::placebos_usize_object::<_T>(DafnyUsize::into_usize(xs.cardinality()));
                    for __i0_0 in integer_range(truncate!(int!(0), usize), rd!(_nw0.clone()).len()) {
                        {
                            let __idx0 = DafnyUsize::into_usize(__i0_0.clone());
                            ::dafny_runtime::md!(_nw0)[__idx0] = MaybeUninit::new((&_init0)(&int!(__i0_0.clone())));
                        }
                    }
                    a = MaybePlacebo::from(array::construct_object(_nw0.clone()));
                    return a.read();
                }
                /// DafnyStandardLibraries-rs.dfy(6601,3)
                pub fn ToSet<_T: DafnyTypeEq>(xs: &Sequence<_T>) -> Set<_T> {
                    (&({
                        let mut xs = xs.clone();
                        Rc::new(move || -> Set<_T>{
            let mut _coll0: SetBuilder<_T> = SetBuilder::<_T>::new();
            for __compr_0 in (&xs).iter() {
                let mut x: _T = __compr_0.clone();
                if xs.contains(&x) {
                    _coll0.add(&x)
                }
            }
            _coll0.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
                    }))()
                }
                /// DafnyStandardLibraries-rs.dfy(6721,3)
                pub fn IndexOf<_T: DafnyTypeEq>(xs: &Sequence<_T>, v: &_T) -> nat {
                    let mut _accumulator: nat = int!(0);
                    let mut _r0 = xs.clone();
                    let mut _r1 = v.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        let v = _r1;
                        if xs.get(&int!(0)) == v.clone() {
                            return int!(0) + _accumulator.clone();
                        } else {
                            _accumulator = _accumulator.clone() + int!(1);
                            let mut _in0: Sequence<_T> = xs.drop(&int!(1));
                            let mut _in1: _T = v.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6732,3)
                pub fn IndexOfOption<_T: DafnyTypeEq>(xs: &Sequence<_T>, v: &_T) -> Rc<Option<nat>> {
                    crate::Std::Collections::Seq::_default::IndexByOption::<_T>(xs, {
                            let v: _T = v.clone();
                            &({
                                let mut v = v.clone();
                                Rc::new(move |x: &_T| -> bool{
            x.clone() == v.clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(6738,3)
                pub fn IndexByOption<_T: DafnyTypeEq>(xs: &Sequence<_T>, p: &Rc<dyn ::std::ops::Fn(&_T) -> bool>) -> Rc<Option<nat>> {
                    if xs.cardinality() == int!(0) {
                        Rc::new(Option::None::<DafnyInt> {})
                    } else {
                        if p(&xs.get(&int!(0))) {
                            Rc::new(Option::Some::<DafnyInt> {
                                    value: int!(0)
                                })
                        } else {
                            let mut _o_k: Rc<Option<nat>> = crate::Std::Collections::Seq::_default::IndexByOption::<_T>(&xs.drop(&int!(1)), p);
                            if matches!((&_o_k).as_ref(), Some{ .. }) {
                                Rc::new(Option::Some::<DafnyInt> {
                                        value: _o_k.value().clone() + int!(1)
                                    })
                            } else {
                                Rc::new(Option::None::<DafnyInt> {})
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6749,3)
                pub fn LastIndexOf<_T: DafnyTypeEq>(xs: &Sequence<_T>, v: &_T) -> nat {
                    let mut _r0 = xs.clone();
                    let mut _r1 = v.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        let v = _r1;
                        if xs.get(&(xs.cardinality() - int!(1))) == v.clone() {
                            return xs.cardinality() - int!(1);
                        } else {
                            let mut _in0: Sequence<_T> = xs.take(&(xs.cardinality() - int!(1)));
                            let mut _in1: _T = v.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6760,3)
                pub fn LastIndexOfOption<_T: DafnyTypeEq>(xs: &Sequence<_T>, v: &_T) -> Rc<Option<nat>> {
                    crate::Std::Collections::Seq::_default::LastIndexByOption::<_T>(xs, {
                            let v: _T = v.clone();
                            &({
                                let mut v = v.clone();
                                Rc::new(move |x: &_T| -> bool{
            x.clone() == v.clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(6766,3)
                pub fn LastIndexByOption<_T: DafnyTypeEq>(xs: &Sequence<_T>, p: &Rc<dyn ::std::ops::Fn(&_T) -> bool>) -> Rc<Option<nat>> {
                    let mut _r0 = xs.clone();
                    let mut _r1 = p.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        let p = _r1;
                        if xs.cardinality() == int!(0) {
                            return Rc::new(Option::None::<DafnyInt> {});
                        } else {
                            if (&p)(&xs.get(&(xs.cardinality() - int!(1)))) {
                                return Rc::new(Option::Some::<DafnyInt> {
                                            value: xs.cardinality() - int!(1)
                                        });
                            } else {
                                let mut _in0: Sequence<_T> = xs.take(&(xs.cardinality() - int!(1)));
                                let mut _in1: Rc<dyn ::std::ops::Fn(&_T) -> bool> = p.clone();
                                _r0 = _in0.clone();
                                _r1 = _in1.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6777,3)
                pub fn Remove<_T: DafnyType>(xs: &Sequence<_T>, pos: &nat) -> Sequence<_T> {
                    xs.take(pos).concat(&xs.drop(&(pos.clone() + int!(1))))
                }
                /// DafnyStandardLibraries-rs.dfy(6786,3)
                pub fn RemoveValue<_T: DafnyTypeEq>(xs: &Sequence<_T>, v: &_T) -> Sequence<_T> {
                    if !xs.contains(v) {
                        xs.clone()
                    } else {
                        let mut i: nat = crate::Std::Collections::Seq::_default::IndexOf::<_T>(xs, v);
                        xs.take(&i).concat(&xs.drop(&(i.clone() + int!(1))))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6798,3)
                pub fn Insert<_T: DafnyType>(xs: &Sequence<_T>, a: &_T, pos: &nat) -> Sequence<_T> {
                    xs.take(pos).concat(&seq![a.clone()]).concat(&xs.drop(pos))
                }
                /// DafnyStandardLibraries-rs.dfy(6810,3)
                pub fn Reverse<_T: DafnyType>(xs: &Sequence<_T>) -> Sequence<_T> {
                    let mut _accumulator: Sequence<_T> = seq![] as Sequence<_T>;
                    let mut _r0 = xs.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        if xs.clone().to_array().len() == 0 {
                            return _accumulator.concat(&(seq![] as Sequence<_T>));
                        } else {
                            _accumulator = _accumulator.concat(&seq![xs.get(&(xs.cardinality() - int!(1)))]);
                            let mut _in0: Sequence<_T> = xs.slice(&int!(0), &(xs.cardinality() - int!(1)));
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6820,3)
                pub fn Repeat<_T: DafnyType>(v: &_T, length: &nat) -> Sequence<_T> {
                    let mut _accumulator: Sequence<_T> = seq![] as Sequence<_T>;
                    let mut _r0 = v.clone();
                    let mut _r1 = length.clone();
                    'TAIL_CALL_START: loop {
                        let v = _r0;
                        let length = _r1;
                        if length.clone() == int!(0) {
                            return _accumulator.concat(&(seq![] as Sequence<_T>));
                        } else {
                            _accumulator = _accumulator.concat(&seq![v.clone()]);
                            let mut _in0: _T = v.clone();
                            let mut _in1: DafnyInt = length.clone() - int!(1);
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6830,3)
                pub fn Unzip<_A: DafnyType, _B: DafnyType>(xs: &Sequence<(_A, _B)>) -> (Sequence<_A>, Sequence<_B>) {
                    if xs.cardinality() == int!(0) {
                        (
                            seq![] as Sequence<_A>,
                            seq![] as Sequence<_B>
                        )
                    } else {
                        let mut __let_tmp_rhs0: (Sequence<_A>, Sequence<_B>) = crate::Std::Collections::Seq::_default::Unzip::<_A, _B>(&crate::Std::Collections::Seq::_default::DropLast::<(_A, _B)>(xs));
                        let mut a: Sequence<_A> = __let_tmp_rhs0.0.clone();
                        let mut b: Sequence<_B> = __let_tmp_rhs0.1.clone();
                        (
                            a.concat(&seq![crate::Std::Collections::Seq::_default::Last::<(_A, _B)>(xs).0.clone()]),
                            b.concat(&seq![crate::Std::Collections::Seq::_default::Last::<(_A, _B)>(xs).1.clone()])
                        )
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6840,3)
                pub fn Zip<_A: DafnyType, _B: DafnyType>(xs: &Sequence<_A>, ys: &Sequence<_B>) -> Sequence<(_A, _B)> {
                    let mut _accumulator: Sequence<(_A, _B)> = seq![] as Sequence<(_A, _B)>;
                    let mut _r0 = xs.clone();
                    let mut _r1 = ys.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        let ys = _r1;
                        if xs.cardinality() == int!(0) {
                            return (seq![] as Sequence<(_A, _B)>).concat(&_accumulator);
                        } else {
                            _accumulator = seq![(
                                        crate::Std::Collections::Seq::_default::Last::<_A>(&xs),
                                        crate::Std::Collections::Seq::_default::Last::<_B>(&ys)
                                    )].concat(&_accumulator);
                            let mut _in0: Sequence<_A> = crate::Std::Collections::Seq::_default::DropLast::<_A>(&xs);
                            let mut _in1: Sequence<_B> = crate::Std::Collections::Seq::_default::DropLast::<_B>(&ys);
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6864,3)
                pub fn Max(xs: &Sequence<DafnyInt>) -> DafnyInt {
                    if xs.cardinality() == int!(1) {
                        xs.get(&int!(0))
                    } else {
                        crate::Std::Math::_default::Max(&xs.get(&int!(0)), &crate::Std::Collections::Seq::_default::Max(&xs.drop(&int!(1))))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6890,3)
                pub fn Min(xs: &Sequence<DafnyInt>) -> DafnyInt {
                    if xs.cardinality() == int!(1) {
                        xs.get(&int!(0))
                    } else {
                        crate::Std::Math::_default::Min(&xs.get(&int!(0)), &crate::Std::Collections::Seq::_default::Min(&xs.drop(&int!(1))))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6938,3)
                pub fn Flatten<_T: DafnyType>(xs: &Sequence<Sequence<_T>>) -> Sequence<_T> {
                    let mut _accumulator: Sequence<_T> = seq![] as Sequence<_T>;
                    let mut _r0 = xs.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        if xs.cardinality() == int!(0) {
                            return _accumulator.concat(&(seq![] as Sequence<_T>));
                        } else {
                            _accumulator = _accumulator.concat(&xs.get(&int!(0)));
                            let mut _in0: Sequence<Sequence<_T>> = xs.drop(&int!(1));
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(6966,3)
                pub fn FlattenReverse<_T: DafnyType>(xs: &Sequence<Sequence<_T>>) -> Sequence<_T> {
                    let mut _accumulator: Sequence<_T> = seq![] as Sequence<_T>;
                    let mut _r0 = xs.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        if xs.cardinality() == int!(0) {
                            return (seq![] as Sequence<_T>).concat(&_accumulator);
                        } else {
                            _accumulator = crate::Std::Collections::Seq::_default::Last::<Sequence<_T>>(&xs).concat(&_accumulator);
                            let mut _in0: Sequence<Sequence<_T>> = crate::Std::Collections::Seq::_default::DropLast::<Sequence<_T>>(&xs);
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7037,3)
                pub fn Join<_T: DafnyType>(seqs: &Sequence<Sequence<_T>>, separator: &Sequence<_T>) -> Sequence<_T> {
                    let mut _accumulator: Sequence<_T> = seq![] as Sequence<_T>;
                    let mut _r0 = seqs.clone();
                    let mut _r1 = separator.clone();
                    'TAIL_CALL_START: loop {
                        let seqs = _r0;
                        let separator = _r1;
                        if seqs.cardinality() == int!(0) {
                            return _accumulator.concat(&(seq![] as Sequence<_T>));
                        } else {
                            if seqs.cardinality() == int!(1) {
                                return _accumulator.concat(&seqs.get(&int!(0)));
                            } else {
                                _accumulator = _accumulator.concat(&seqs.get(&int!(0)).concat(&separator));
                                let mut _in0: Sequence<Sequence<_T>> = seqs.drop(&int!(1));
                                let mut _in1: Sequence<_T> = separator.clone();
                                _r0 = _in0.clone();
                                _r1 = _in1.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7052,3)
                pub fn Split<_T: DafnyTypeEq>(s: &Sequence<_T>, delim: &_T) -> Sequence<Sequence<_T>> {
                    let mut _accumulator: Sequence<Sequence<_T>> = seq![] as Sequence<Sequence<_T>>;
                    let mut _r0 = s.clone();
                    let mut _r1 = delim.clone();
                    'TAIL_CALL_START: loop {
                        let s = _r0;
                        let delim = _r1;
                        let mut i: Rc<Option<nat>> = crate::Std::Collections::Seq::_default::IndexOfOption::<_T>(&s, &delim);
                        if matches!((&i).as_ref(), Some{ .. }) {
                            _accumulator = _accumulator.concat(&seq![s.take(i.value())]);
                            let mut _in0: Sequence<_T> = s.drop(&(i.value().clone() + int!(1)));
                            let mut _in1: _T = delim.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        } else {
                            return _accumulator.concat(&seq![s.clone()]);
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7067,3)
                pub fn SplitOnce<_T: DafnyTypeEq>(s: &Sequence<_T>, delim: &_T) -> (Sequence<_T>, Sequence<_T>) {
                    let mut i: Rc<Option<nat>> = crate::Std::Collections::Seq::_default::IndexOfOption::<_T>(s, delim);
                    (
                        s.take(i.value()),
                        s.drop(&(i.value().clone() + int!(1)))
                    )
                }
                /// DafnyStandardLibraries-rs.dfy(7077,3)
                pub fn SplitOnceOption<_T: DafnyTypeEq>(s: &Sequence<_T>, delim: &_T) -> Rc<Option<(Sequence<_T>, Sequence<_T>)>> {
                    let mut valueOrError0: Rc<Option<nat>> = crate::Std::Collections::Seq::_default::IndexOfOption::<_T>(s, delim);
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<(Sequence<_T>, Sequence<_T>)>()
                    } else {
                        let mut i: nat = valueOrError0.Extract();
                        Rc::new(Option::Some::<(Sequence<_T>, Sequence<_T>)> {
                                value: (
                                        s.take(&i),
                                        s.drop(&(i.clone() + int!(1)))
                                    )
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7138,3)
                pub fn Map<_T: DafnyType, _R: DafnyType>(f: &Rc<dyn ::std::ops::Fn(&_T) -> _R>, xs: &Sequence<_T>) -> Sequence<_R> {
                    let mut _accumulator: Sequence<_R> = seq![] as Sequence<_R>;
                    let mut _r0 = f.clone();
                    let mut _r1 = xs.clone();
                    'TAIL_CALL_START: loop {
                        let f = _r0;
                        let xs = _r1;
                        if xs.cardinality() == int!(0) {
                            return _accumulator.concat(&(seq![] as Sequence<_R>));
                        } else {
                            _accumulator = _accumulator.concat(&seq![(&f)(&xs.get(&int!(0)))]);
                            let mut _in0: Rc<dyn ::std::ops::Fn(&_T) -> _R> = f.clone();
                            let mut _in1: Sequence<_T> = xs.drop(&int!(1));
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7150,3)
                pub fn MapPartialFunction<_T: DafnyType, _R: DafnyType>(f: &Rc<dyn ::std::ops::Fn(&_T) -> _R>, xs: &Sequence<_T>) -> Sequence<_R> {
                    crate::Std::Collections::Seq::_default::Map::<_T, _R>(f, xs)
                }
                /// DafnyStandardLibraries-rs.dfy(7156,3)
                pub fn MapWithResult<_T: DafnyType, _R: DafnyType, _E: DafnyType>(f: &Rc<dyn ::std::ops::Fn(&_T) -> Rc<crate::Std::Wrappers::Result<_R, _E>>>, xs: &Sequence<_T>) -> Rc<crate::Std::Wrappers::Result<Sequence<_R>, _E>> {
                    if xs.cardinality() == int!(0) {
                        Rc::new(crate::Std::Wrappers::Result::Success::<Sequence<_R>, _E> {
                                value: seq![] as Sequence<_R>
                            })
                    } else {
                        let mut valueOrError0: Rc<crate::Std::Wrappers::Result<_R, _E>> = f(&xs.get(&int!(0)));
                        if valueOrError0.IsFailure() {
                            valueOrError0.PropagateFailure::<Sequence<_R>>()
                        } else {
                            let mut head: _R = valueOrError0.Extract();
                            let mut valueOrError1: Rc<crate::Std::Wrappers::Result<Sequence<_R>, _E>> = crate::Std::Collections::Seq::_default::MapWithResult::<_T, _R, _E>(f, &xs.drop(&int!(1)));
                            if valueOrError1.IsFailure() {
                                valueOrError1.PropagateFailure::<Sequence<_R>>()
                            } else {
                                let mut tail: Sequence<_R> = valueOrError1.Extract();
                                Rc::new(crate::Std::Wrappers::Result::Success::<Sequence<_R>, _E> {
                                        value: seq![head.clone()].concat(&tail)
                                    })
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7215,3)
                pub fn Filter<_T: DafnyType>(f: &Rc<dyn ::std::ops::Fn(&_T) -> bool>, xs: &Sequence<_T>) -> Sequence<_T> {
                    let mut _accumulator: Sequence<_T> = seq![] as Sequence<_T>;
                    let mut _r0 = f.clone();
                    let mut _r1 = xs.clone();
                    'TAIL_CALL_START: loop {
                        let f = _r0;
                        let xs = _r1;
                        if xs.cardinality() == int!(0) {
                            return _accumulator.concat(&(seq![] as Sequence<_T>));
                        } else {
                            _accumulator = _accumulator.concat(&(if (&f)(&xs.get(&int!(0))) {
                                        seq![xs.get(&int!(0))]
                                    } else {
                                        seq![] as Sequence<_T>
                                    }));
                            let mut _in0: Rc<dyn ::std::ops::Fn(&_T) -> bool> = f.clone();
                            let mut _in1: Sequence<_T> = xs.drop(&int!(1));
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7257,3)
                pub fn FoldLeft<_A: DafnyType, _T: DafnyType>(f: &Rc<dyn ::std::ops::Fn(&_A, &_T) -> _A>, init: &_A, xs: &Sequence<_T>) -> _A {
                    let mut _r0 = f.clone();
                    let mut _r1 = init.clone();
                    let mut _r2 = xs.clone();
                    'TAIL_CALL_START: loop {
                        let f = _r0;
                        let init = _r1;
                        let xs = _r2;
                        if xs.cardinality() == int!(0) {
                            return init.clone();
                        } else {
                            let mut _in0: Rc<dyn ::std::ops::Fn(&_A, &_T) -> _A> = f.clone();
                            let mut _in1: _A = (&f)(&init, &xs.get(&int!(0)));
                            let mut _in2: Sequence<_T> = xs.drop(&int!(1));
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            _r2 = _in2.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7310,3)
                pub fn FoldRight<_A: DafnyType, _T: DafnyType>(f: &Rc<dyn ::std::ops::Fn(&_T, &_A) -> _A>, xs: &Sequence<_T>, init: &_A) -> _A {
                    if xs.cardinality() == int!(0) {
                        init.clone()
                    } else {
                        f(&xs.get(&int!(0)), &crate::Std::Collections::Seq::_default::FoldRight::<_A, _T>(f, &xs.drop(&int!(1)), init))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7357,3)
                pub fn MergeSortBy<_T: DafnyType>(lessThanOrEq: &Rc<dyn ::std::ops::Fn(&_T, &_T) -> bool>, a: &Sequence<_T>) -> Sequence<_T> {
                    if !(int!(1) < a.cardinality()) {
                        a.clone()
                    } else {
                        let mut splitIndex: DafnyInt = euclidian_division(a.cardinality(), int!(2));
                        let mut left: Sequence<_T> = a.take(&splitIndex);
                        let mut right: Sequence<_T> = a.drop(&splitIndex);
                        let mut leftSorted: Sequence<_T> = crate::Std::Collections::Seq::_default::MergeSortBy::<_T>(lessThanOrEq, &left);
                        let mut rightSorted: Sequence<_T> = crate::Std::Collections::Seq::_default::MergeSortBy::<_T>(lessThanOrEq, &right);
                        crate::Std::Collections::Seq::_default::MergeSortedWith::<_T>(&leftSorted, &rightSorted, lessThanOrEq)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7368,3)
                pub fn MergeSortedWith<_T: DafnyType>(left: &Sequence<_T>, right: &Sequence<_T>, lessThanOrEq: &Rc<dyn ::std::ops::Fn(&_T, &_T) -> bool>) -> Sequence<_T> {
                    let mut _accumulator: Sequence<_T> = seq![] as Sequence<_T>;
                    let mut _r0 = left.clone();
                    let mut _r1 = right.clone();
                    let mut _r2 = lessThanOrEq.clone();
                    'TAIL_CALL_START: loop {
                        let left = _r0;
                        let right = _r1;
                        let lessThanOrEq = _r2;
                        if left.cardinality() == int!(0) {
                            return _accumulator.concat(&right);
                        } else {
                            if right.cardinality() == int!(0) {
                                return _accumulator.concat(&left);
                            } else {
                                if (&lessThanOrEq)(&left.get(&int!(0)), &right.get(&int!(0))) {
                                    _accumulator = _accumulator.concat(&seq![left.get(&int!(0))]);
                                    let mut _in0: Sequence<_T> = left.drop(&int!(1));
                                    let mut _in1: Sequence<_T> = right.clone();
                                    let mut _in2: Rc<dyn ::std::ops::Fn(&_T, &_T) -> bool> = lessThanOrEq.clone();
                                    _r0 = _in0.clone();
                                    _r1 = _in1.clone();
                                    _r2 = _in2.clone();
                                    continue 'TAIL_CALL_START;
                                } else {
                                    _accumulator = _accumulator.concat(&seq![right.get(&int!(0))]);
                                    let mut _in3: Sequence<_T> = left.clone();
                                    let mut _in4: Sequence<_T> = right.drop(&int!(1));
                                    let mut _in5: Rc<dyn ::std::ops::Fn(&_T, &_T) -> bool> = lessThanOrEq.clone();
                                    _r0 = _in3.clone();
                                    _r1 = _in4.clone();
                                    _r2 = _in5.clone();
                                    continue 'TAIL_CALL_START;
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7416,3)
                pub fn All<_T: DafnyType>(s: &Sequence<_T>, p: &Rc<dyn ::std::ops::Fn(&_T) -> bool>) -> bool {
                    integer_range(int!(0), s.cardinality()).all(({
                            let mut p = p.clone();
                            let mut s = s.clone();
                            Rc::new(move |__forall_var_0: DafnyInt| -> bool{
            let mut i: DafnyInt = __forall_var_0.clone();
            !(!(i.clone() < int!(0)) && i.clone() < s.cardinality()) || (&p)(&s.get(&i))
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                        }).as_ref())
                }
                /// DafnyStandardLibraries-rs.dfy(7422,3)
                pub fn AllNot<_T: DafnyType>(s: &Sequence<_T>, p: &Rc<dyn ::std::ops::Fn(&_T) -> bool>) -> bool {
                    integer_range(int!(0), s.cardinality()).all(({
                            let mut p = p.clone();
                            let mut s = s.clone();
                            Rc::new(move |__forall_var_0: DafnyInt| -> bool{
            let mut i: DafnyInt = __forall_var_0.clone();
            !(!(i.clone() < int!(0)) && i.clone() < s.cardinality()) || !(&p)(&s.get(&i))
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                        }).as_ref())
                }
                /// DafnyStandardLibraries-rs.dfy(7462,3)
                pub fn Partitioned<_T: DafnyType>(s: &Sequence<_T>, p: &Rc<dyn ::std::ops::Fn(&_T) -> bool>) -> bool {
                    let mut _r0 = s.clone();
                    let mut _r1 = p.clone();
                    'TAIL_CALL_START: loop {
                        let s = _r0;
                        let p = _r1;
                        if s.clone().to_array().len() == 0 {
                            return true;
                        } else {
                            if (&p)(&s.get(&int!(0))) {
                                let mut _in0: Sequence<_T> = s.drop(&int!(1));
                                let mut _in1: Rc<dyn ::std::ops::Fn(&_T) -> bool> = p.clone();
                                _r0 = _in0.clone();
                                _r1 = _in1.clone();
                                continue 'TAIL_CALL_START;
                            } else {
                                return crate::Std::Collections::Seq::_default::AllNot::<_T>(&s.drop(&int!(1)), &p);
                            }
                        }
                    }
                }
            }

            /// DafnyStandardLibraries-rs.dfy(7560,3)
            #[derive(Clone)]
            pub enum Slice<T: DafnyType> {
                Slice {
                    data: Sequence<T>,
                    start: DafnyInt,
                    end: DafnyInt
                }
            }

            impl<T: DafnyType> Slice<T> {
                /// DafnyStandardLibraries-rs.dfy(7566,5)
                pub fn View(&self) -> Sequence<T> {
                    self.data().slice(self.start(), self.end())
                }
                /// DafnyStandardLibraries-rs.dfy(7572,5)
                pub fn Length(&self) -> nat {
                    self.end().clone() - self.start().clone()
                }
                /// DafnyStandardLibraries-rs.dfy(7578,5)
                pub fn At(&self, i: &DafnyInt) -> T {
                    self.data().get(&(self.start().clone() + i.clone()))
                }
                /// DafnyStandardLibraries-rs.dfy(7586,5)
                pub fn Drop(&self, firstIncludedIndex: &DafnyInt) -> Rc<crate::Std::Collections::Seq::Slice<T>> {
                    Rc::new(crate::Std::Collections::Seq::Slice::Slice::<T> {
                            data: self.data().clone(),
                            start: self.start().clone() + firstIncludedIndex.clone(),
                            end: self.end().clone()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(7595,5)
                pub fn Sub(&self, firstIncludedIndex: &DafnyInt, lastExcludedIndex: &DafnyInt) -> Rc<crate::Std::Collections::Seq::Slice<T>> {
                    Rc::new(crate::Std::Collections::Seq::Slice::Slice::<T> {
                            data: self.data().clone(),
                            start: self.start().clone() + firstIncludedIndex.clone(),
                            end: self.start().clone() + lastExcludedIndex.clone()
                        })
                }
                /// Returns a borrow of the field data
                pub fn data(&self) -> &Sequence<T> {
                    match self {
                        Slice::Slice{data, start, end, } => data,
                    }
                }
                /// Returns a borrow of the field start
                pub fn start(&self) -> &DafnyInt {
                    match self {
                        Slice::Slice{data, start, end, } => start,
                    }
                }
                /// Returns a borrow of the field end
                pub fn end(&self) -> &DafnyInt {
                    match self {
                        Slice::Slice{data, start, end, } => end,
                    }
                }
            }

            impl<T: DafnyType> Debug
                for Slice<T> {
                fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<T: DafnyType> DafnyPrint
                for Slice<T> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        Slice::Slice{data, start, end, } => {
                            write!(_formatter, "Std.Collections.Seq.Slice.Slice(")?;
                            DafnyPrint::fmt_print(data, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(start, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(end, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<T: DafnyType + Eq + Hash> PartialEq
                for Slice<T> {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (Slice::Slice{data, start, end, }, Slice::Slice{data: _2_data, start: _2_start, end: _2_end, }) => {
                            data == _2_data && start == _2_start && end == _2_end
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl<T: DafnyType + Eq + Hash> Eq
                for Slice<T> {}

            impl<T: DafnyType + Hash> Hash
                for Slice<T> {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        Slice::Slice{data, start, end, } => {
                            Hash::hash(data, _state);
                            Hash::hash(start, _state);
                            Hash::hash(end, _state)
                        },
                    }
                }
            }

            impl<T: DafnyType> AsRef<Slice<T>>
                for Slice<T> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(7630,1)
        pub mod Set {
            pub use ::dafny_runtime::DafnyTypeEq;
            pub use ::dafny_runtime::Set;
            pub use ::std::rc::Rc;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::MaybePlacebo;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::SetBuilder;
            pub use ::dafny_runtime::set;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(7712,3)
                pub fn ExtractFromSingleton<_T: DafnyTypeEq>(s: &Set<_T>) -> _T {
                    (&({
                        let mut s = s.clone();
                        Rc::new(move |__let_dummy_0: &DafnyInt| -> _T{
            let mut x = MaybePlacebo::<_T>::new();
            'label_goto__ASSIGN_SUCH_THAT_0: loop {
                for __assign_such_that_0 in (&s).iter().cloned() {
                    x = MaybePlacebo::from(__assign_such_that_0.clone());
                    if s.contains(&x.read()) {
                        break 'label_goto__ASSIGN_SUCH_THAT_0;
                    }
                }
                panic!("Halt");
                break;
            };
            x.read()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                    }))(&int!(0))
                }
                /// DafnyStandardLibraries-rs.dfy(7736,3)
                pub fn Map<_X: DafnyTypeEq, _Y: DafnyTypeEq>(f: &Rc<dyn ::std::ops::Fn(&_X) -> _Y>, xs: &Set<_X>) -> Set<_Y> {
                    let mut ys: Set<_Y> = (&({
                            let mut f = f.clone();
                            let mut xs = xs.clone();
                            Rc::new(move || -> Set<_Y>{
            let mut _coll0: SetBuilder<_Y> = SetBuilder::<_Y>::new();
            for __compr_0 in (&xs).iter().cloned() {
                let mut x: _X = __compr_0.clone();
                if xs.contains(&x) {
                    _coll0.add(&(&f)(&x))
                }
            }
            _coll0.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
                        }))();
                    ys.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(7762,3)
                pub fn Filter<_X: DafnyTypeEq>(f: &Rc<dyn ::std::ops::Fn(&_X) -> bool>, xs: &Set<_X>) -> Set<_X> {
                    let mut ys: Set<_X> = (&({
                            let mut f = f.clone();
                            let mut xs = xs.clone();
                            Rc::new(move || -> Set<_X>{
            let mut _coll0: SetBuilder<_X> = SetBuilder::<_X>::new();
            for __compr_0 in (&xs).iter().cloned() {
                let mut x: _X = __compr_0.clone();
                if xs.contains(&x) && (&f)(&x) {
                    _coll0.add(&x)
                }
            }
            _coll0.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
                        }))();
                    ys.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(7793,3)
                pub fn SetRange(a: &DafnyInt, b: &DafnyInt) -> Set<DafnyInt> {
                    let mut _accumulator: Set<DafnyInt> = set!{};
                    let mut _r0 = a.clone();
                    let mut _r1 = b.clone();
                    'TAIL_CALL_START: loop {
                        let a = _r0;
                        let b = _r1;
                        if a.clone() == b.clone() {
                            return set!{}.merge(&_accumulator);
                        } else {
                            _accumulator = _accumulator.merge(&set!{a.clone()});
                            let mut _in0: DafnyInt = a.clone() + int!(1);
                            let mut _in1: DafnyInt = b.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7805,3)
                pub fn SetRangeZeroBound(n: &DafnyInt) -> Set<DafnyInt> {
                    crate::Std::Collections::Set::_default::SetRange(&int!(0), n)
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(7914,1)
        pub mod Tuple {
            pub use ::dafny_runtime::DafnyType;
            pub use ::std::rc::Rc;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(7915,3)
                pub fn T2_0<_L: DafnyType, _R: DafnyType>() -> Rc<dyn ::std::ops::Fn(&(_L, _R)) -> _L> {
                    {
                        Rc::new(move |lr: &(_L, _R)| -> _L{
            lr.0.clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(7920,3)
                pub fn T2_1<_L: DafnyType, _R: DafnyType>() -> Rc<dyn ::std::ops::Fn(&(_L, _R)) -> _R> {
                    {
                        Rc::new(move |lr: &(_L, _R)| -> _R{
            lr.1.clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                    }
                }
            }
        }
    }

    /// DafnyStandardLibraries-rs.dfy(7926,1)
    pub mod DynamicArray {
        pub use ::dafny_runtime::DafnyType;
        pub use ::dafny_runtime::Object;
        pub use ::dafny_runtime::allocate_object;
        pub use ::dafny_runtime::update_field_mut_uninit_object;
        pub use ::dafny_runtime::int;
        pub use ::std::mem::MaybeUninit;
        pub use ::dafny_runtime::array;
        pub use ::dafny_runtime::DafnyUsize;
        pub use ::dafny_runtime::_System::nat;
        pub use ::dafny_runtime::rd;
        pub use ::dafny_runtime::read_field;
        pub use ::dafny_runtime::DafnyInt;
        pub use ::dafny_runtime::modify_field;
        pub use ::std::rc::Rc;
        pub use ::dafny_runtime::integer_range;
        pub use ::dafny_runtime::truncate;
        pub use ::dafny_runtime::UpcastObject;
        pub use ::dafny_runtime::DynAny;
        pub use ::dafny_runtime::UpcastObjectFn;

        /// DafnyStandardLibraries-rs.dfy(7936,3)
        pub struct DynamicArray<A: DafnyType> {
            pub size: ::dafny_runtime::Field<nat>,
            pub capacity: ::dafny_runtime::Field<nat>,
            pub data: ::dafny_runtime::Field<Object<[A]>>
        }

        impl<A: DafnyType> DynamicArray<A> {
            /// Allocates an UNINITIALIZED instance. Only the Dafny compiler should use that.
            pub fn _allocate_object() -> Object<Self> {
                allocate_object::<Self>()
            }
            /// DafnyStandardLibraries-rs.dfy(7953,5)
            pub fn _ctor(this: &Object<crate::Std::DynamicArray::DynamicArray<A>>) -> () {
                let mut _set_size: bool = false;
                let mut _set_capacity: bool = false;
                let mut _set_data: bool = false;
                update_field_mut_uninit_object!(this.clone(), size, _set_size, int!(0));
                update_field_mut_uninit_object!(this.clone(), capacity, _set_capacity, int!(0));
                let mut _nw0: Object<[MaybeUninit<A>]> = array::placebos_usize_object::<A>(DafnyUsize::into_usize(int!(0)));
                update_field_mut_uninit_object!(this.clone(), data, _set_data, array::construct_object(_nw0.clone()));
                return ();
            }
            /// DafnyStandardLibraries-rs.dfy(7967,5)
            pub fn At(&self, index: &nat) -> A {
                rd!(read_field!(self.data))[DafnyUsize::into_usize(index.clone())].clone()
            }
            /// DafnyStandardLibraries-rs.dfy(7976,5)
            pub fn Put(&self, index: &nat, element: &A) -> () {
                {
                    let __idx0 = DafnyUsize::into_usize(index.clone());
                    ::dafny_runtime::md!(::dafny_runtime::read_field!(self.data))[__idx0] = element.clone();
                };
                return ();
            }
            /// DafnyStandardLibraries-rs.dfy(7990,5)
            pub fn Ensure(&self, reserved: &nat, defaultValue: &A) -> () {
                let mut newCapacity: DafnyInt = read_field!(self.capacity);
                while newCapacity.clone() - read_field!(self.size) < reserved.clone() {
                    newCapacity = self.DefaultNewCapacity(&newCapacity);
                };
                if read_field!(self.capacity) < newCapacity.clone() {
                    self.Realloc(defaultValue, &newCapacity)
                };
                return ();
            }
            /// DafnyStandardLibraries-rs.dfy(8011,5)
            pub fn PopFast(&self) -> () {
                modify_field!(self.size, read_field!(self.size) - int!(1));
                return ();
            }
            /// DafnyStandardLibraries-rs.dfy(8025,5)
            pub fn PushFast(&self, element: &A) -> () {
                {
                    let __idx0 = DafnyUsize::into_usize(read_field!(self.size));
                    ::dafny_runtime::md!(::dafny_runtime::read_field!(self.data))[__idx0] = element.clone();
                };
                modify_field!(self.size, read_field!(self.size) + int!(1));
                return ();
            }
            /// DafnyStandardLibraries-rs.dfy(8041,5)
            pub fn Push(&self, element: &A) -> () {
                if read_field!(self.size) == read_field!(self.capacity) {
                    self.ReallocDefault(element)
                };
                self.PushFast(element);
                return ();
            }
            /// DafnyStandardLibraries-rs.dfy(8057,5)
            pub fn Realloc(&self, defaultValue: &A, newCapacity: &nat) -> () {
                let mut oldData: Object<[A]>;
                let mut oldCapacity: nat;
                let mut _rhs0: Object<[A]> = read_field!(self.data);
                let mut _rhs1: nat = read_field!(self.capacity);
                oldData = _rhs0.clone();
                oldCapacity = _rhs1.clone();
                let mut _init0: Rc<dyn ::std::ops::Fn(&nat) -> A> = {
                        let defaultValue: A = defaultValue.clone();
                        {
                            let mut defaultValue = defaultValue.clone();
                            Rc::new(move |_v0: &nat| -> A{
            defaultValue.clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    };
                let mut _nw0: Object<[MaybeUninit<A>]> = array::placebos_usize_object::<A>(DafnyUsize::into_usize(newCapacity.clone()));
                for __i0_0 in integer_range(truncate!(int!(0), usize), rd!(_nw0.clone()).len()) {
                    {
                        let __idx0 = DafnyUsize::into_usize(__i0_0.clone());
                        ::dafny_runtime::md!(_nw0)[__idx0] = MaybeUninit::new((&_init0)(&int!(__i0_0.clone())));
                    }
                }
                let mut _rhs2: Object<[A]> = array::construct_object(_nw0.clone());
                let mut _rhs3: nat = newCapacity.clone();
                let mut _lhs0: Object<crate::Std::DynamicArray::DynamicArray<A>> = Object::<_>::from_ref(self);
                let mut _lhs1: Object<crate::Std::DynamicArray::DynamicArray<A>> = Object::<_>::from_ref(self);
                modify_field!(rd!(_lhs0).data, _rhs2.clone());
                modify_field!(rd!(_lhs1).capacity, _rhs3.clone());
                self.CopyFrom(&oldData, &oldCapacity);
                return ();
            }
            /// DafnyStandardLibraries-rs.dfy(8072,5)
            pub fn DefaultNewCapacity(&self, capacity: &nat) -> nat {
                if capacity.clone() == int!(0) {
                    int!(8)
                } else {
                    int!(2) * capacity.clone()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(8080,5)
            pub fn ReallocDefault(&self, defaultValue: &A) -> () {
                self.Realloc(defaultValue, &self.DefaultNewCapacity(&read_field!(self.capacity)));
                return ();
            }
            /// DafnyStandardLibraries-rs.dfy(8091,5)
            pub fn CopyFrom(&self, newData: &Object<[A]>, count: &nat) -> () {
                for __guard_loop_0 in integer_range(int!(0), count.clone()) {
                    let mut index: DafnyInt = __guard_loop_0.clone();
                    if true && (!(index.clone() < int!(0)) && index.clone() < count.clone()) {
                        {
                            let __idx0 = DafnyUsize::into_usize(index.clone());
                            ::dafny_runtime::md!(::dafny_runtime::read_field!(self.data))[__idx0] = rd!(newData)[DafnyUsize::into_usize(index.clone())].clone();
                        }
                    }
                }
                return ();
            }
        }

        impl<A: DafnyType> UpcastObject<DynAny>
            for crate::Std::DynamicArray::DynamicArray<A> {
            UpcastObjectFn!(DynAny);
        }
    }

    /// DafnyStandardLibraries-rs.dfy(147,1)
    pub mod FileIO {
        pub use ::dafny_runtime::Sequence;
        pub use ::dafny_runtime::DafnyChar;
        pub use ::std::rc::Rc;
        pub use crate::Std::Wrappers::Result;
        pub use ::dafny_runtime::MaybePlacebo;
        pub use ::dafny_runtime::DafnyInt;
        pub use ::dafny_runtime::integer_range;
        pub use ::dafny_runtime::Zero;
        pub use crate::Std::Wrappers::Outcome;
        pub use ::dafny_runtime::string_of;

        pub struct _default {}

        impl _default {
            /// DafnyStandardLibraries-rs.dfy(148,3)
            pub fn ReadBytesFromFile(path: &Sequence<DafnyChar>) -> Rc<Result<Sequence<u8>, Sequence<DafnyChar>>> {
                let mut res: Rc<Result<Sequence<u8>, Sequence<DafnyChar>>>;
                let mut isError: bool;
                let mut bytesRead: Sequence<u8>;
                let mut errorMsg: Sequence<DafnyChar>;
                let mut _out0: bool;
                let mut _out1: Sequence<u8>;
                let mut _out2: Sequence<DafnyChar>;
                let _x = crate::Std::FileIOInternalExterns::_default::INTERNAL_ReadBytesFromFile(path);
                _out0 = _x.0;
                _out1 = _x.1;
                _out2 = _x.2;
                isError = _out0;
                bytesRead = _out1.clone();
                errorMsg = _out2.clone();
                if isError {
                    res = Rc::new(Result::Failure::<Sequence<u8>, Sequence<DafnyChar>> {
                                error: errorMsg.clone()
                            });
                } else {
                    res = Rc::new(Result::Success::<Sequence<u8>, Sequence<DafnyChar>> {
                                value: bytesRead.clone()
                            });
                };
                return res.clone();
            }
            /// DafnyStandardLibraries-rs.dfy(154,3)
            pub fn WriteBytesToFile(path: &Sequence<DafnyChar>, bytes: &Sequence<u8>) -> Rc<Result<(), Sequence<DafnyChar>>> {
                let mut res: Rc<Result<(), Sequence<DafnyChar>>>;
                let mut isError: bool;
                let mut errorMsg: Sequence<DafnyChar>;
                let mut _out0: bool;
                let mut _out1: Sequence<DafnyChar>;
                let _x = crate::Std::FileIOInternalExterns::_default::INTERNAL_WriteBytesToFile(path, bytes);
                _out0 = _x.0;
                _out1 = _x.1;
                isError = _out0;
                errorMsg = _out1.clone();
                if isError {
                    res = Rc::new(Result::Failure::<(), Sequence<DafnyChar>> {
                                error: errorMsg.clone()
                            });
                } else {
                    res = Rc::new(Result::Success::<(), Sequence<DafnyChar>> {
                                value: ()
                            });
                };
                return res.clone();
            }
            /// DafnyStandardLibraries-rs.dfy(160,3)
            pub fn ReadUTF8FromFile(fileName: &Sequence<DafnyChar>) -> Rc<Result<Sequence<DafnyChar>, Sequence<DafnyChar>>> {
                let mut r = MaybePlacebo::<Rc<Result<Sequence<DafnyChar>, Sequence<DafnyChar>>>>::new();
                let mut valueOrError0: Rc<Result<Sequence<u8>, Sequence<DafnyChar>>>;
                let mut _out0: Rc<Result<Sequence<u8>, Sequence<DafnyChar>>>;
                _out0 = crate::Std::FileIO::_default::ReadBytesFromFile(fileName);
                valueOrError0 = _out0.clone();
                if valueOrError0.IsFailure() {
                    r = MaybePlacebo::from(valueOrError0.PropagateFailure::<Sequence<DafnyChar>>());
                    return r.read();
                };
                let mut bytes: Sequence<u8> = valueOrError0.Extract();
                r = MaybePlacebo::from(crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::FromUTF8Checked(&({
                                let _initializer = {
                                        let bytes: Sequence<u8> = bytes.clone();
                                        {
                                            let mut bytes = bytes.clone();
                                            Rc::new(move |i: &DafnyInt| -> u8{
            bytes.get(i) as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }
                                    };
                                integer_range(Zero::zero(), bytes.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                            })));
                return r.read();
            }
            /// DafnyStandardLibraries-rs.dfy(166,3)
            pub fn WriteUTF8ToFile(fileName: &Sequence<DafnyChar>, content: &Sequence<DafnyChar>) -> Rc<Outcome<Sequence<DafnyChar>>> {
                let mut r = MaybePlacebo::<Rc<Outcome<Sequence<DafnyChar>>>>::new();
                let mut bytes: Sequence<u8> = crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ToUTF8Checked(content).value().clone();
                let mut writeResult: Rc<Result<(), Sequence<DafnyChar>>>;
                let mut _out0: Rc<Result<(), Sequence<DafnyChar>>>;
                _out0 = crate::Std::FileIO::_default::WriteBytesToFile(fileName, &({
                            let _initializer = {
                                    let bytes: Sequence<u8> = bytes.clone();
                                    {
                                        let mut bytes = bytes.clone();
                                        Rc::new(move |i: &DafnyInt| -> u8{
            bytes.get(i) as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                    }
                                };
                            integer_range(Zero::zero(), bytes.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                        }));
                writeResult = _out0.clone();
                if writeResult.IsFailure() {
                    r = MaybePlacebo::from(Rc::new(Outcome::Fail::<Sequence<DafnyChar>> {
                                    error: string_of("Failed to write to file '").concat(fileName).concat(&string_of("': ")).concat(writeResult.error())
                                }));
                    return r.read();
                };
                r = MaybePlacebo::from(Rc::new(Outcome::Pass::<Sequence<DafnyChar>> {}));
                return r.read();
            }
        }
    }

    /// DafnyStandardLibraries-rs.dfy(8107,1)
    pub mod Functions {
        
    }

    /// DafnyStandardLibraries-rs.dfy(8134,1)
    pub mod Math {
        pub use ::dafny_runtime::DafnyInt;
        pub use ::dafny_runtime::int;

        pub struct _default {}

        impl _default {
            /// DafnyStandardLibraries-rs.dfy(8135,3)
            pub fn Min(a: &DafnyInt, b: &DafnyInt) -> DafnyInt {
                if a.clone() < b.clone() {
                    a.clone()
                } else {
                    b.clone()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(8143,3)
            pub fn Min3(a: &DafnyInt, b: &DafnyInt, c: &DafnyInt) -> DafnyInt {
                crate::Std::Math::_default::Min(a, &crate::Std::Math::_default::Min(b, c))
            }
            /// DafnyStandardLibraries-rs.dfy(8148,3)
            pub fn Max(a: &DafnyInt, b: &DafnyInt) -> DafnyInt {
                if a.clone() < b.clone() {
                    b.clone()
                } else {
                    a.clone()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(8156,3)
            pub fn Max3(a: &DafnyInt, b: &DafnyInt, c: &DafnyInt) -> DafnyInt {
                crate::Std::Math::_default::Max(a, &crate::Std::Math::_default::Max(b, c))
            }
            /// DafnyStandardLibraries-rs.dfy(8161,3)
            pub fn Abs(a: &DafnyInt) -> DafnyInt {
                if a.clone() < int!(0) {
                    int!(0) - a.clone()
                } else {
                    a.clone()
                }
            }
        }
    }

    pub mod Parsers {
        /// DafnyStandardLibraries-rs.dfy(9296,1)
        pub mod InputString {
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::std::rc::Rc;
            pub use crate::Std::Collections::Seq::Slice;
            pub use ::dafny_runtime::int;
            pub use ::std::convert::AsRef;
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::DafnyInt;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(9297,3)
                pub fn ToInput(r: &Sequence<DafnyChar>) -> crate::Std::Parsers::InputString::Input {
                    Rc::new(Slice::Slice::<DafnyChar> {
                            data: r.clone(),
                            start: int!(0),
                            end: r.cardinality()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(9303,3)
                pub fn View(_self: &crate::Std::Parsers::InputString::Input) -> Sequence<DafnyChar> {
                    Slice::<DafnyChar>::View(AsRef::as_ref(_self))
                }
                /// DafnyStandardLibraries-rs.dfy(9309,3)
                pub fn Length(_self: &crate::Std::Parsers::InputString::Input) -> nat {
                    Slice::<DafnyChar>::Length(AsRef::as_ref(_self))
                }
                /// DafnyStandardLibraries-rs.dfy(9314,3)
                pub fn CharAt(_self: &crate::Std::Parsers::InputString::Input, i: &DafnyInt) -> DafnyChar {
                    Slice::<DafnyChar>::At(AsRef::as_ref(_self), i)
                }
                /// DafnyStandardLibraries-rs.dfy(9320,3)
                pub fn Drop(_self: &crate::Std::Parsers::InputString::Input, start: &DafnyInt) -> crate::Std::Parsers::InputString::Input {
                    Slice::<DafnyChar>::Drop(AsRef::as_ref(_self), start)
                }
                /// DafnyStandardLibraries-rs.dfy(9326,3)
                pub fn Slice(_self: &crate::Std::Parsers::InputString::Input, start: &DafnyInt, end: &DafnyInt) -> crate::Std::Parsers::InputString::Input {
                    Slice::<DafnyChar>::Sub(AsRef::as_ref(_self), start, end)
                }
                /// DafnyStandardLibraries-rs.dfy(9337,3)
                pub fn Equals(_self: &crate::Std::Parsers::InputString::Input, other: &crate::Std::Parsers::InputString::Input) -> bool {
                    _self.clone() == other.clone()
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9345,3)
            pub type Input = Rc<Slice<DafnyChar>>;
        }

        /// DafnyStandardLibraries-rs.dfy(9227,1)
        pub mod StringBuilders {
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::DafnyChar;
            pub use crate::Std::Parsers::InputString::Input;
            pub use ::std::rc::Rc;
            pub use crate::Std::Collections::Seq::Slice;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::string_of;
            pub use ::dafny_runtime::DafnyType;
            pub use crate::Std::Parsers::StringParsers::ParseResult;
            pub use crate::Std::Parsers::StringParsers::FailureLevel;
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::seq;
            pub use crate::Std::Parsers::StringBuilders::RecNoStackResult::RecReturn;
            pub use ::dafny_runtime::Map;
            pub use crate::Std::Parsers::StringParsers::RecursiveDef;
            pub use ::dafny_runtime::MapBuilder;
            pub use crate::Std::Wrappers::Option;
            pub use ::std::fmt::Debug;
            pub use ::std::fmt::Formatter;
            pub use ::std::fmt::Result;
            pub use ::dafny_runtime::DafnyPrint;
            pub use ::std::convert::AsRef;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(9228,3)
                pub fn ToInput(other: &Sequence<DafnyChar>) -> Input {
                    Rc::new(Slice::Slice::<DafnyChar> {
                            data: other.clone(),
                            start: int!(0),
                            end: other.cardinality()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(9234,3)
                pub fn ToInputEnd(other: &Sequence<DafnyChar>, fromEnd: &DafnyInt) -> Input {
                    Rc::new(Slice::Slice::<DafnyChar> {
                            data: other.clone(),
                            start: other.cardinality() - fromEnd.clone(),
                            end: other.cardinality()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(9241,3)
                pub fn S(s: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<DafnyChar>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<DafnyChar>> {
                            apply: crate::Std::Parsers::StringParsers::_default::String(s)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(9246,3)
                pub fn String(s: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<DafnyChar>>> {
                    crate::Std::Parsers::StringBuilders::_default::S(s)
                }
                /// DafnyStandardLibraries-rs.dfy(9258,3)
                pub fn Except(s: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<DafnyChar>>> {
                    crate::Std::Parsers::StringBuilders::_default::CharTest({
                            let s: Sequence<DafnyChar> = s.clone();
                            &({
                                let mut s = s.clone();
                                Rc::new(move |c: &DafnyChar| -> bool{
            !s.contains(c)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            })
                        }, &string_of("Not '").concat(s).concat(&string_of("'"))).Rep()
                }
                /// DafnyStandardLibraries-rs.dfy(9263,3)
                pub fn DebugSummaryInput(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                    crate::Std::Parsers::StringParsers::_default::DebugSummaryInput(name, input)
                }
                /// DafnyStandardLibraries-rs.dfy(9268,3)
                pub fn PrintDebugSummaryOutput<_R: DafnyType>(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>, result: &Rc<ParseResult<_R>>) -> () {
                    crate::Std::Parsers::StringParsers::_default::PrintDebugSummaryOutput::<_R>(name, input, result);
                    return ();
                }
                /// DafnyStandardLibraries-rs.dfy(9273,3)
                pub fn FailureToString<_R: DafnyType>(input: &Sequence<DafnyChar>, result: &Rc<ParseResult<_R>>) -> Sequence<DafnyChar> {
                    crate::Std::Parsers::StringParsers::_default::FailureToString::<_R>(input, result, &int!(-1))
                }
                /// DafnyStandardLibraries-rs.dfy(9279,3)
                pub fn Apply<_T: DafnyType>(parser: &Rc<crate::Std::Parsers::StringBuilders::B<_T>>, input: &Sequence<DafnyChar>) -> Rc<ParseResult<_T>> {
                    crate::Std::Parsers::StringParsers::_default::Apply::<_T>(parser.apply(), input)
                }
                /// DafnyStandardLibraries-rs.dfy(9284,3)
                pub fn InputToString(input: &Input) -> Sequence<DafnyChar> {
                    crate::Std::Parsers::InputString::_default::View(input)
                }
                /// DafnyStandardLibraries-rs.dfy(8173,3)
                pub fn SucceedWith<_T: DafnyType>(t: &_T) -> Rc<crate::Std::Parsers::StringBuilders::B<_T>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_T> {
                            apply: crate::Std::Parsers::StringParsers::_default::SucceedWith::<_T>(t)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8178,3)
                pub fn FailWith<_T: DafnyType>(message: &Sequence<DafnyChar>, level: &Rc<FailureLevel>) -> Rc<crate::Std::Parsers::StringBuilders::B<_T>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_T> {
                            apply: crate::Std::Parsers::StringParsers::_default::FailWith::<_T>(message, level)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8183,3)
                pub fn ResultWith<_R: DafnyType>(result: &Rc<ParseResult<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_R> {
                            apply: crate::Std::Parsers::StringParsers::_default::ResultWith::<_R>(result)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8190,3)
                pub fn MId<_R: DafnyType>(r: &_R) -> _R {
                    r.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(8195,3)
                pub fn MapIdentity<_R: DafnyType>(r: &_R) -> _R {
                    r.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(8200,3)
                pub fn O<_R: DafnyType>(alternatives: &Sequence<Rc<crate::Std::Parsers::StringBuilders::B<_R>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    if alternatives.cardinality() == int!(0) {
                        crate::Std::Parsers::StringBuilders::_default::FailWith::<_R>(&string_of("no alternative"), &Rc::new(FailureLevel::Recoverable {}))
                    } else {
                        if alternatives.cardinality() == int!(1) {
                            alternatives.get(&int!(0))
                        } else {
                            Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_R> {
                                    apply: crate::Std::Parsers::StringParsers::_default::Or::<_R>(alternatives.get(&int!(0)).apply(), crate::Std::Parsers::StringBuilders::_default::O::<_R>(&alternatives.drop(&int!(1))).apply())
                                })
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8210,3)
                pub fn Or<_R: DafnyType>(alternatives: &Sequence<Rc<crate::Std::Parsers::StringBuilders::B<_R>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    crate::Std::Parsers::StringBuilders::_default::O::<_R>(alternatives)
                }
                /// DafnyStandardLibraries-rs.dfy(8218,3)
                pub fn CharTest(test: &Rc<dyn ::std::ops::Fn(&DafnyChar) -> bool>, name: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<DafnyChar>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<DafnyChar> {
                            apply: crate::Std::Parsers::StringParsers::_default::CharTest(test, name)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8223,3)
                pub fn Rec<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringBuilders::B<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_R> {
                            apply: crate::Std::Parsers::StringParsers::_default::Recursive::<_R>({
                                        let underlying: Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringBuilders::B<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>>> = underlying.clone();
                                        &({
                                            let mut underlying = underlying.clone();
                                            Rc::new(move |p: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<_R>>>| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<_R>>>{
            (&underlying)(&Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_R> {
                        apply: p.clone()
                    })).apply().clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        })
                                    })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8228,3)
                pub fn Recursive<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringBuilders::B<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    crate::Std::Parsers::StringBuilders::_default::Rec::<_R>(underlying)
                }
                /// DafnyStandardLibraries-rs.dfy(8233,3)
                pub fn InputLength(input: &Input) -> nat {
                    crate::Std::Parsers::InputString::_default::Length(input)
                }
                /// DafnyStandardLibraries-rs.dfy(8238,3)
                pub fn NonProgressing(input1: &Input, input2: &Input) -> bool {
                    !(crate::Std::Parsers::StringBuilders::_default::InputLength(input2) < crate::Std::Parsers::StringBuilders::_default::InputLength(input1))
                }
                /// DafnyStandardLibraries-rs.dfy(8243,3)
                pub fn RecursiveProgressError<_R: DafnyType>(name: &Sequence<DafnyChar>, input1: &Input, input2: &Input) -> Rc<ParseResult<_R>> {
                    crate::Std::Parsers::StringParsers::_default::RecursiveProgressError::<_R>(name, input1, input2)
                }
                /// DafnyStandardLibraries-rs.dfy(8249,3)
                pub fn RecNoStack<_R: DafnyType>(underlying: &Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_R> {
                            apply: {
                                    let underlying: Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>> = underlying.clone();
                                    {
                                        let mut underlying = underlying.clone();
                                        Rc::new(move |input: &Input| -> Rc<ParseResult<_R>>{
            crate::Std::Parsers::StringBuilders::_default::RecNoStack_::<_R>(&underlying, &underlying, input, input, &(seq![] as Sequence<Rc<dyn ::std::ops::Fn(&Rc<ParseResult<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>>>))
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                    }
                                }
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8254,3)
                pub fn RecursiveNoStack<_R: DafnyType>(underlying: &Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    crate::Std::Parsers::StringBuilders::_default::RecNoStack::<_R>(underlying)
                }
                /// DafnyStandardLibraries-rs.dfy(8259,3)
                pub fn RecNoStack_<_R: DafnyType>(continuation: &Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>, underlying: &Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>, input: &Input, previousInput: &Input, callbacks: &Sequence<Rc<dyn ::std::ops::Fn(&Rc<ParseResult<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>>>) -> Rc<ParseResult<_R>> {
                    let mut _r0 = continuation.clone();
                    let mut _r1 = underlying.clone();
                    let mut _r2 = input.clone();
                    let mut _r3 = previousInput.clone();
                    let mut _r4 = callbacks.clone();
                    'TAIL_CALL_START: loop {
                        let continuation = _r0;
                        let underlying = _r1;
                        let input = _r2;
                        let previousInput = _r3;
                        let callbacks = _r4;
                        let mut continuationResult: Rc<ParseResult<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>> = continuation.apply()(&input);
                        let mut remaining: Input = continuationResult.Remaining();
                        if continuationResult.IsFailure() || matches!((&continuationResult.Extract().0.clone()).as_ref(), RecReturn{ .. }) {
                            let mut parseResult: Rc<ParseResult<_R>> = if continuationResult.IsFailure() {
                                    continuationResult.PropagateFailure::<_R>()
                                } else {
                                    Rc::new(ParseResult::ParseSuccess::<_R> {
                                            result: continuationResult.Extract().0.clone().toReturn().clone(),
                                            remaining: remaining.clone()
                                        })
                                };
                            if callbacks.cardinality() == int!(0) {
                                return parseResult.clone();
                            } else {
                                let mut toCompute: Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>> = (&callbacks.get(&int!(0)))(&parseResult);
                                if crate::Std::Parsers::InputString::_default::Length(&input) < crate::Std::Parsers::InputString::_default::Length(&remaining) {
                                    return crate::Std::Parsers::StringBuilders::_default::RecursiveProgressError::<_R>(&string_of("Parsers.RecNoStack[internal]"), &input, &remaining);
                                } else {
                                    if crate::Std::Parsers::InputString::_default::Length(&previousInput) < crate::Std::Parsers::InputString::_default::Length(&input) {
                                        return crate::Std::Parsers::StringBuilders::_default::RecursiveProgressError::<_R>(&string_of("Parsers.RecNoStack[internal]"), &previousInput, &input);
                                    } else {
                                        let mut _in0: Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>> = toCompute.clone();
                                        let mut _in1: Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>> = underlying.clone();
                                        let mut _in2: Input = remaining.clone();
                                        let mut _in3: Input = input.clone();
                                        let mut _in4: Sequence<Rc<dyn ::std::ops::Fn(&Rc<ParseResult<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>>> = callbacks.drop(&int!(1));
                                        _r0 = _in0.clone();
                                        _r1 = _in1.clone();
                                        _r2 = _in2.clone();
                                        _r3 = _in3.clone();
                                        _r4 = _in4.clone();
                                        continue 'TAIL_CALL_START;
                                    }
                                }
                            }
                        } else {
                            let mut recursor: Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>> = continuationResult.Extract().0.clone();
                            let mut rToNewParserOfRecursiveNoStackResultOfR: Rc<dyn ::std::ops::Fn(&_R, &Input) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>> = recursor.toContinue().clone();
                            if crate::Std::Parsers::InputString::_default::Length(&remaining) < crate::Std::Parsers::InputString::_default::Length(&input) {
                                let mut _in5: Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>> = underlying.clone();
                                let mut _in6: Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>> = underlying.clone();
                                let mut _in7: Input = remaining.clone();
                                let mut _in8: Input = remaining.clone();
                                let mut _in9: Sequence<Rc<dyn ::std::ops::Fn(&Rc<ParseResult<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>>> = seq![{
                                            let rToNewParserOfRecursiveNoStackResultOfR: Rc<dyn ::std::ops::Fn(&_R, &Input) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>> = rToNewParserOfRecursiveNoStackResultOfR.clone();
                                            {
                                                let mut rToNewParserOfRecursiveNoStackResultOfR = rToNewParserOfRecursiveNoStackResultOfR.clone();
                                                Rc::new(move |p: &Rc<ParseResult<_R>>| -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>{
            if p.IsFailure() {
                Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>> {
                        apply: crate::Std::Parsers::StringParsers::_default::ResultWith::<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>(&p.PropagateFailure::<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>())
                    })
            } else {
                {
                    let __pat_let1_0: (_R, Input) = p.Extract();
                    {
                        let r: _R = __pat_let1_0.0.clone();
                        {
                            let remaining2: Input = __pat_let1_0.1.clone();
                            (&rToNewParserOfRecursiveNoStackResultOfR)(&r, &remaining2)
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                            }
                                        }].concat(&callbacks);
                                _r0 = _in5.clone();
                                _r1 = _in6.clone();
                                _r2 = _in7.clone();
                                _r3 = _in8.clone();
                                _r4 = _in9.clone();
                                continue 'TAIL_CALL_START;
                            } else {
                                if crate::Std::Parsers::InputString::_default::Length(&remaining) == crate::Std::Parsers::InputString::_default::Length(&input) && crate::Std::Parsers::InputString::_default::Length(&remaining) < crate::Std::Parsers::InputString::_default::Length(&previousInput) {
                                    let mut _in10: Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>> = underlying.clone();
                                    let mut _in11: Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>> = underlying.clone();
                                    let mut _in12: Input = remaining.clone();
                                    let mut _in13: Input = remaining.clone();
                                    let mut _in14: Sequence<Rc<dyn ::std::ops::Fn(&Rc<ParseResult<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>>> = seq![{
                                                let rToNewParserOfRecursiveNoStackResultOfR: Rc<dyn ::std::ops::Fn(&_R, &Input) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>> = rToNewParserOfRecursiveNoStackResultOfR.clone();
                                                {
                                                    let mut rToNewParserOfRecursiveNoStackResultOfR = rToNewParserOfRecursiveNoStackResultOfR.clone();
                                                    Rc::new(move |p: &Rc<ParseResult<_R>>| -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>{
            if p.IsFailure() {
                Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>> {
                        apply: crate::Std::Parsers::StringParsers::_default::ResultWith::<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>(&p.PropagateFailure::<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>())
                    })
            } else {
                {
                    let __pat_let2_0: (_R, Input) = p.Extract();
                    {
                        let r: _R = __pat_let2_0.0.clone();
                        {
                            let remaining2: Input = __pat_let2_0.1.clone();
                            (&rToNewParserOfRecursiveNoStackResultOfR)(&r, &remaining2)
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                                }
                                            }].concat(&callbacks);
                                    _r0 = _in10.clone();
                                    _r1 = _in11.clone();
                                    _r2 = _in12.clone();
                                    _r3 = _in13.clone();
                                    _r4 = _in14.clone();
                                    continue 'TAIL_CALL_START;
                                } else {
                                    return crate::Std::Parsers::StringBuilders::_default::RecursiveProgressError::<_R>(&string_of("ParserBuilders.RecNoStack"), &input, &remaining);
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8274,3)
                pub fn RecMap<_R: DafnyType>(underlying: &Map<Sequence<DafnyChar>, Rc<crate::Std::Parsers::StringBuilders::RecMapDef<_R>>>, startFun: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_R> {
                            apply: crate::Std::Parsers::StringParsers::_default::RecursiveMap::<_R>(&(&({
                                        let mut underlying = underlying.clone();
                                        Rc::new(move || -> Map<Sequence<DafnyChar>, Rc<RecursiveDef<_R>>>{
            let mut _coll0: MapBuilder<Sequence<DafnyChar>, Rc<RecursiveDef<_R>>> = MapBuilder::<Sequence<DafnyChar>, Rc<RecursiveDef<_R>>>::new();
            for __compr_0 in (&underlying).keys().iter().cloned() {
                let mut k: Sequence<DafnyChar> = __compr_0.clone();
                if underlying.contains(&k) {
                    _coll0.add(&k, &Rc::new(RecursiveDef::RecursiveDef::<_R> {
                                order: underlying.get(&k).order().clone(),
                                definition: {
                                        let underlying: Map<Sequence<DafnyChar>, Rc<crate::Std::Parsers::StringBuilders::RecMapDef<_R>>> = underlying.clone();
                                        let k: Sequence<DafnyChar> = k.clone();
                                        {
                                            let mut underlying = underlying.clone();
                                            let mut k = k.clone();
                                            Rc::new(move |selector: &Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<_R>>>>| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<_R>>>{
            underlying.get(&k).definition()({
                    let selector: Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<_R>>>> = selector.clone();
                    &({
                        let mut selector = selector.clone();
                        Rc::new(move |name: &Sequence<DafnyChar>| -> Rc<crate::Std::Parsers::StringBuilders::B<_R>>{
            Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_R> {
                    apply: (&selector)(name)
                })
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                    })
                }).apply().clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }
                                    }
                            }))
                }
            }
            _coll0.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
                                    }))(), startFun)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8279,3)
                pub fn RecursiveMap<_R: DafnyType>(underlying: &Map<Sequence<DafnyChar>, Rc<crate::Std::Parsers::StringBuilders::RecMapDef<_R>>>, startFun: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    crate::Std::Parsers::StringBuilders::_default::RecMap::<_R>(underlying, startFun)
                }
                /// DafnyStandardLibraries-rs.dfy(9251,3)
                pub fn Int() -> Rc<crate::Std::Parsers::StringBuilders::B<DafnyInt>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<DafnyInt> {
                            apply: crate::Std::Parsers::StringParsers::_default::Int()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(9252,3)
                pub fn Nat() -> Rc<crate::Std::Parsers::StringBuilders::B<nat>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<nat> {
                            apply: crate::Std::Parsers::StringParsers::_default::Nat()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(9253,3)
                pub fn Digit() -> Rc<crate::Std::Parsers::StringBuilders::B<DafnyChar>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<DafnyChar> {
                            apply: crate::Std::Parsers::StringParsers::_default::Digit()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(9254,3)
                pub fn DigitNumber() -> Rc<crate::Std::Parsers::StringBuilders::B<nat>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<nat> {
                            apply: crate::Std::Parsers::StringParsers::_default::DigitNumber()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(9255,3)
                pub fn WS() -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<DafnyChar>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<DafnyChar>> {
                            apply: crate::Std::Parsers::StringParsers::_default::WS()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(9256,3)
                pub fn Whitespace() -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<DafnyChar>>> {
                    crate::Std::Parsers::StringBuilders::_default::WS()
                }
                /// DafnyStandardLibraries-rs.dfy(8188,3)
                pub fn Nothing() -> Rc<crate::Std::Parsers::StringBuilders::B<()>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<()> {
                            apply: crate::Std::Parsers::StringParsers::_default::Epsilon()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8215,3)
                pub fn EOS() -> Rc<crate::Std::Parsers::StringBuilders::B<()>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<()> {
                            apply: crate::Std::Parsers::StringParsers::_default::EndOfString()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8216,3)
                pub fn EndOfString() -> Rc<crate::Std::Parsers::StringBuilders::B<()>> {
                    crate::Std::Parsers::StringBuilders::_default::EOS()
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8301,3)
            #[derive(Clone)]
            pub enum B<R: DafnyType> {
                B {
                    apply: Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<R>>>
                }
            }

            impl<R: DafnyType> B<R> {
                /// DafnyStandardLibraries-rs.dfy(8302,5)
                pub fn Apply(&self, input: &Sequence<DafnyChar>) -> Rc<ParseResult<R>> {
                    self.apply()(&crate::Std::Parsers::StringBuilders::_default::ToInput(input))
                }
                /// DafnyStandardLibraries-rs.dfy(8307,5)
                pub fn _q(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<Option<R>>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Rc<Option<R>>> {
                            apply: crate::Std::Parsers::StringParsers::_default::Maybe::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8312,5)
                pub fn Option(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<Option<R>>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Rc<Option<R>>> {
                            apply: crate::Std::Parsers::StringParsers::_default::Maybe::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8317,5)
                pub fn __q_q(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::_q::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8322,5)
                pub fn FailureResetsInput(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::_q::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8327,5)
                pub fn e_I<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_U> {
                            apply: crate::Std::Parsers::StringParsers::_default::ConcatKeepRight::<R, _U>(self.apply(), other.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8332,5)
                pub fn ConcatKeepRight<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    self.e_I::<_U>(other)
                }
                /// DafnyStandardLibraries-rs.dfy(8337,5)
                pub fn I_e<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::ConcatKeepLeft::<R, _U>(self.apply(), other.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8342,5)
                pub fn ConcatKeepLeft<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    self.I_e::<_U>(other)
                }
                /// DafnyStandardLibraries-rs.dfy(8347,5)
                pub fn I_I<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<(R, _U)>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<(R, _U)> {
                            apply: crate::Std::Parsers::StringParsers::_default::Concat::<R, _U>(self.apply(), other.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8352,5)
                pub fn Concat<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<(R, _U)>> {
                    self.I_I::<_U>(other)
                }
                /// DafnyStandardLibraries-rs.dfy(8357,5)
                pub fn If<_U: DafnyType>(&self, cond: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::If::<_U, R>(cond.apply(), self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8362,5)
                pub fn M<_U: DafnyType>(&self, mappingFunc: &Rc<dyn ::std::ops::Fn(&R) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_U> {
                            apply: crate::Std::Parsers::StringParsers::_default::Map::<R, _U>(self.apply(), mappingFunc)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8367,5)
                pub fn Map<_U: DafnyType>(&self, mappingFunc: &Rc<dyn ::std::ops::Fn(&R) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    self.M::<_U>(mappingFunc)
                }
                /// DafnyStandardLibraries-rs.dfy(8372,5)
                pub fn M2<_R1: DafnyType, _R2: DafnyType, _U: DafnyType>(&self, unfolder: &Rc<dyn ::std::ops::Fn(&R) -> (_R1, _R2)>, mappingFunc: &Rc<dyn ::std::ops::Fn(&_R1, &_R2) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_U> {
                            apply: crate::Std::Parsers::StringParsers::_default::Map::<R, _U>(self.apply(), {
                                        let unfolder: Rc<dyn ::std::ops::Fn(&R) -> (_R1, _R2)> = unfolder.clone();
                                        let mappingFunc: Rc<dyn ::std::ops::Fn(&_R1, &_R2) -> _U> = mappingFunc.clone();
                                        &({
                                            let mut unfolder = unfolder.clone();
                                            let mut mappingFunc = mappingFunc.clone();
                                            Rc::new(move |x: &R| -> _U{
            {
                let __pat_let3_0: (_R1, _R2) = (&unfolder)(x);
                {
                    let x: (_R1, _R2) = __pat_let3_0.clone();
                    (&mappingFunc)(&x.0.clone(), &x.1.clone())
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        })
                                    })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8377,5)
                pub fn Map2<_R1: DafnyType, _R2: DafnyType, _U: DafnyType>(&self, unfolder: &Rc<dyn ::std::ops::Fn(&R) -> (_R1, _R2)>, mappingFunc: &Rc<dyn ::std::ops::Fn(&_R1, &_R2) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    self.M2::<_R1, _R2, _U>(unfolder, mappingFunc)
                }
                /// DafnyStandardLibraries-rs.dfy(8382,5)
                pub fn M3<_R1: DafnyType, _R2: DafnyType, _R3: DafnyType, _U: DafnyType>(&self, unfolder: &Rc<dyn ::std::ops::Fn(&R) -> (_R1, _R2, _R3)>, mappingFunc: &Rc<dyn ::std::ops::Fn(&_R1, &_R2, &_R3) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_U> {
                            apply: crate::Std::Parsers::StringParsers::_default::Map::<R, _U>(self.apply(), {
                                        let unfolder: Rc<dyn ::std::ops::Fn(&R) -> (_R1, _R2, _R3)> = unfolder.clone();
                                        let mappingFunc: Rc<dyn ::std::ops::Fn(&_R1, &_R2, &_R3) -> _U> = mappingFunc.clone();
                                        &({
                                            let mut unfolder = unfolder.clone();
                                            let mut mappingFunc = mappingFunc.clone();
                                            Rc::new(move |x: &R| -> _U{
            {
                let __pat_let4_0: (_R1, _R2, _R3) = (&unfolder)(x);
                {
                    let x: (_R1, _R2, _R3) = __pat_let4_0.clone();
                    (&mappingFunc)(&x.0.clone(), &x.1.clone(), &x.2.clone())
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        })
                                    })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8387,5)
                pub fn Map3<_R1: DafnyType, _R2: DafnyType, _R3: DafnyType, _U: DafnyType>(&self, unfolder: &Rc<dyn ::std::ops::Fn(&R) -> (_R1, _R2, _R3)>, mappingFunc: &Rc<dyn ::std::ops::Fn(&_R1, &_R2, &_R3) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    self.M3::<_R1, _R2, _R3, _U>(unfolder, mappingFunc)
                }
                /// DafnyStandardLibraries-rs.dfy(8392,5)
                pub fn Then<_V: DafnyType>(&self, other: &Rc<dyn ::std::ops::Fn(&R) -> Rc<crate::Std::Parsers::StringBuilders::B<_V>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_V>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_V> {
                            apply: crate::Std::Parsers::StringParsers::_default::Bind::<R, _V>(self.apply(), {
                                        let other: Rc<dyn ::std::ops::Fn(&R) -> Rc<crate::Std::Parsers::StringBuilders::B<_V>>> = other.clone();
                                        &({
                                            let mut other = other.clone();
                                            Rc::new(move |result: &R| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<_V>>>{
            (&other)(result).apply().clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        })
                                    })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8397,5)
                pub fn ThenWithRemaining<_V: DafnyType>(&self, other: &Rc<dyn ::std::ops::Fn(&R, &Input) -> Rc<crate::Std::Parsers::StringBuilders::B<_V>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_V>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_V> {
                            apply: crate::Std::Parsers::StringParsers::_default::BindSucceeds::<R, _V>(self.apply(), {
                                        let other: Rc<dyn ::std::ops::Fn(&R, &Input) -> Rc<crate::Std::Parsers::StringBuilders::B<_V>>> = other.clone();
                                        &({
                                            let mut other = other.clone();
                                            Rc::new(move |result: &R,input: &Input| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<_V>>>{
            (&other)(result, input).apply().clone()
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                                        })
                                    })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8402,5)
                pub fn Bind<_V: DafnyType>(&self, other: &Rc<dyn ::std::ops::Fn(&Rc<ParseResult<R>>, &Input) -> Rc<crate::Std::Parsers::StringBuilders::B<_V>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_V>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_V> {
                            apply: crate::Std::Parsers::StringParsers::_default::BindResult::<R, _V>(self.apply(), {
                                        let other: Rc<dyn ::std::ops::Fn(&Rc<ParseResult<R>>, &Input) -> Rc<crate::Std::Parsers::StringBuilders::B<_V>>> = other.clone();
                                        &({
                                            let mut other = other.clone();
                                            Rc::new(move |result: &Rc<ParseResult<R>>,input: &Input| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<_V>>>{
            (&other)(result, input).apply().clone()
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                                        })
                                    })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8407,5)
                pub fn Debug<_D: DafnyType>(&self, name: &Sequence<DafnyChar>, onEnter: &Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>, &Input) -> _D>, onExit: &Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>, &_D, &Rc<ParseResult<R>>) -> ()>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::Debug::<R, _D>(self.apply(), name, onEnter, onExit)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8412,5)
                pub fn RepFold<_A: DafnyType>(&self, init: &_A, combine: &Rc<dyn ::std::ops::Fn(&_A, &R) -> _A>) -> Rc<crate::Std::Parsers::StringBuilders::B<_A>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_A> {
                            apply: crate::Std::Parsers::StringParsers::_default::Rep::<_A, R>(self.apply(), combine, init)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8417,5)
                pub fn RepeatFold<_A: DafnyType>(&self, init: &_A, combine: &Rc<dyn ::std::ops::Fn(&_A, &R) -> _A>) -> Rc<crate::Std::Parsers::StringBuilders::B<_A>> {
                    self.RepFold::<_A>(init, combine)
                }
                /// DafnyStandardLibraries-rs.dfy(8422,5)
                pub fn RepSep<_K: DafnyType>(&self, separator: &Rc<crate::Std::Parsers::StringBuilders::B<_K>>) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<R>> {
                            apply: crate::Std::Parsers::StringParsers::_default::RepSep::<R, _K>(self.apply(), separator.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8427,5)
                pub fn RepeatSeparator<_K: DafnyType>(&self, separator: &Rc<crate::Std::Parsers::StringBuilders::B<_K>>) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    self.RepSep::<_K>(separator)
                }
                /// DafnyStandardLibraries-rs.dfy(8432,5)
                pub fn RepMerge(&self, merger: &Rc<dyn ::std::ops::Fn(&R, &R) -> R>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::RepMerge::<R>(self.apply(), merger)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8437,5)
                pub fn RepeatMerge(&self, merger: &Rc<dyn ::std::ops::Fn(&R, &R) -> R>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    self.RepMerge(merger)
                }
                /// DafnyStandardLibraries-rs.dfy(8442,5)
                pub fn RepSepMerge<_K: DafnyType>(&self, separator: &Rc<crate::Std::Parsers::StringBuilders::B<_K>>, merger: &Rc<dyn ::std::ops::Fn(&R, &R) -> R>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::RepSepMerge::<R, _K>(self.apply(), separator.apply(), merger)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8447,5)
                pub fn RepeatSeparatorMerge<_K: DafnyType>(&self, separator: &Rc<crate::Std::Parsers::StringBuilders::B<_K>>, merger: &Rc<dyn ::std::ops::Fn(&R, &R) -> R>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    self.RepSepMerge::<_K>(separator, merger)
                }
                /// DafnyStandardLibraries-rs.dfy(8452,5)
                pub fn Rep(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<R>> {
                            apply: crate::Std::Parsers::StringParsers::_default::ZeroOrMore::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8457,5)
                pub fn Repeat(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    self.Rep()
                }
                /// DafnyStandardLibraries-rs.dfy(8462,5)
                pub fn Rep1(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<R>> {
                            apply: crate::Std::Parsers::StringParsers::_default::OneOrMore::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8467,5)
                pub fn RepeatAtLeastOnce(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    self.Rep1()
                }
                /// DafnyStandardLibraries-rs.dfy(8472,5)
                pub fn End(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    self.I_e::<()>(&crate::Std::Parsers::StringBuilders::_default::EOS())
                }
                /// Returns a borrow of the field apply
                pub fn apply(&self) -> &Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<R>>> {
                    match self {
                        B::B{apply, } => apply,
                    }
                }
            }

            impl<R: DafnyType> Debug
                for B<R> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<R: DafnyType> DafnyPrint
                for B<R> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        B::B{apply, } => {
                            write!(_formatter, "Std.Parsers.StringBuilders.B.B(")?;
                            write!(_formatter, "<function>")?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<R: DafnyType> AsRef<B<R>>
                for B<R> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8478,3)
            #[derive(Clone)]
            pub enum RecNoStackResult<R: DafnyType> {
                RecReturn {
                    toReturn: R
                },
                RecContinue {
                    toContinue: Rc<dyn ::std::ops::Fn(&R, &Input) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<R>>>>>
                }
            }

            impl<R: DafnyType> RecNoStackResult<R> {
                /// Gets the field toReturn for all enum members which have it
                pub fn toReturn(&self) -> &R {
                    match self {
                        RecNoStackResult::RecReturn{toReturn, } => toReturn,
                        RecNoStackResult::RecContinue{toContinue, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field toContinue for all enum members which have it
                pub fn toContinue(&self) -> &Rc<dyn ::std::ops::Fn(&R, &Input) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<R>>>>> {
                    match self {
                        RecNoStackResult::RecReturn{toReturn, } => panic!("field does not exist on this variant"),
                        RecNoStackResult::RecContinue{toContinue, } => toContinue,
                    }
                }
            }

            impl<R: DafnyType> Debug
                for RecNoStackResult<R> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<R: DafnyType> DafnyPrint
                for RecNoStackResult<R> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        RecNoStackResult::RecReturn{toReturn, } => {
                            write!(_formatter, "Std.Parsers.StringBuilders.RecNoStackResult.RecReturn(")?;
                            DafnyPrint::fmt_print(toReturn, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        RecNoStackResult::RecContinue{toContinue, } => {
                            write!(_formatter, "Std.Parsers.StringBuilders.RecNoStackResult.RecContinue(")?;
                            write!(_formatter, "<function>")?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<R: DafnyType> AsRef<RecNoStackResult<R>>
                for RecNoStackResult<R> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8482,3)
            #[derive(Clone)]
            pub enum RecMapDef<R: DafnyType> {
                RecMapDef {
                    order: nat,
                    definition: Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>>>
                }
            }

            impl<R: DafnyType> RecMapDef<R> {
                /// Returns a borrow of the field order
                pub fn order(&self) -> &nat {
                    match self {
                        RecMapDef::RecMapDef{order, definition, } => order,
                    }
                }
                /// Returns a borrow of the field definition
                pub fn definition(&self) -> &Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>>> {
                    match self {
                        RecMapDef::RecMapDef{order, definition, } => definition,
                    }
                }
            }

            impl<R: DafnyType> Debug
                for RecMapDef<R> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<R: DafnyType> DafnyPrint
                for RecMapDef<R> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        RecMapDef::RecMapDef{order, definition, } => {
                            write!(_formatter, "Std.Parsers.StringBuilders.RecMapDef.RecMapDef(")?;
                            DafnyPrint::fmt_print(order, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            write!(_formatter, "<function>")?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<R: DafnyType> AsRef<RecMapDef<R>>
                for RecMapDef<R> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(9352,1)
        pub mod StringParsers {
            pub use ::dafny_runtime::DafnyChar;
            pub use ::std::rc::Rc;
            pub use crate::Std::Parsers::InputString::Input;
            pub use ::dafny_runtime::seq;
            pub use ::dafny_runtime::string_of;
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::int;
            pub use crate::Std::Wrappers::Option;
            pub use ::std::primitive::char;
            pub use crate::Std::Wrappers::Option::Some;
            pub use crate::Std::Collections::Seq::Slice;
            pub use ::std::convert::AsRef;
            pub use ::dafny_runtime::MaybePlacebo;
            pub use ::dafny_runtime::DafnyPrintWrapper;
            pub use ::dafny_runtime::DafnyType;
            pub use crate::Std::Parsers::StringParsers::ParseResult::ParseFailure;
            pub use crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess;
            pub use crate::Std::Wrappers::Option::None;
            pub use crate::Std::Parsers::StringParsers::RecursiveNoStackResult::RecursiveReturn;
            pub use ::dafny_runtime::Map;
            pub use ::std::fmt::Debug;
            pub use ::std::fmt::Formatter;
            pub use ::std::fmt::Result;
            pub use ::dafny_runtime::DafnyPrint;
            pub use ::std::cmp::PartialEq;
            pub use ::std::cmp::Eq;
            pub use ::std::hash::Hash;
            pub use ::std::hash::Hasher;
            pub use ::dafny_runtime::SequenceIter;
            pub use crate::Std::Parsers::StringParsers::FailureLevel::Fatal;
            pub use ::dafny_runtime::upcast_id;
            pub use crate::Std::Parsers::StringParsers::SeqB::SeqBNil;
            pub use ::dafny_runtime::Object;
            pub use ::std::mem::MaybeUninit;
            pub use ::dafny_runtime::array;
            pub use ::dafny_runtime::DafnyUsize;
            pub use ::dafny_runtime::integer_range;
            pub use ::dafny_runtime::truncate;
            pub use ::dafny_runtime::rd;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(9353,3)
                pub fn Char(expectedChar: &DafnyChar) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<DafnyChar>>> {
                    crate::Std::Parsers::StringParsers::_default::CharTest({
                            let expectedChar: DafnyChar = expectedChar.clone();
                            &({
                                let mut expectedChar = expectedChar.clone();
                                Rc::new(move |c: &DafnyChar| -> bool{
            c.clone() == expectedChar.clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            })
                        }, &seq![expectedChar.clone()])
                }
                /// DafnyStandardLibraries-rs.dfy(9358,3)
                pub fn Space() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<DafnyChar>>> {
                    crate::Std::Parsers::StringParsers::_default::CharTest(&({
                            Rc::new(move |c: &DafnyChar| -> bool{
            string_of(" \t\r\n               　").contains(c)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), &string_of("space"))
                }
                /// DafnyStandardLibraries-rs.dfy(9363,3)
                pub fn WS() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Sequence<DafnyChar>>>> {
                    crate::Std::Parsers::StringParsers::_default::ZeroOrMore::<DafnyChar>(&crate::Std::Parsers::StringParsers::_default::Space())
                }
                /// DafnyStandardLibraries-rs.dfy(9368,3)
                pub fn Digit() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<DafnyChar>>> {
                    crate::Std::Parsers::StringParsers::_default::CharTest(&({
                            Rc::new(move |c: &DafnyChar| -> bool{
            string_of("0123456789").contains(c)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), &string_of("digit"))
                }
                /// DafnyStandardLibraries-rs.dfy(9373,3)
                pub fn DigitNumber() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<nat>>> {
                    crate::Std::Parsers::StringParsers::_default::Map::<DafnyChar, nat>(&crate::Std::Parsers::StringParsers::_default::Digit(), &({
                            Rc::new(move |c: &DafnyChar| -> nat{
            {
                let __pat_let5_0: DafnyInt = crate::Std::Parsers::StringParsers::_default::DigitToInt(c);
                {
                    let d: DafnyInt = __pat_let5_0.clone();
                    {
                        let __pat_let6_0: DafnyInt = if !(d.clone() < int!(0)) {
                                d.clone()
                            } else {
                                int!(0)
                            };
                        {
                            let n: nat = __pat_let6_0.clone();
                            n.clone()
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(9378,3)
                pub fn Nat() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<nat>>> {
                    crate::Std::Parsers::StringParsers::_default::Bind::<nat, nat>(&crate::Std::Parsers::StringParsers::_default::DigitNumber(), &({
                            Rc::new(move |result: &nat| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<nat>>>{
            crate::Std::Parsers::StringParsers::_default::Rep::<nat, nat>(&crate::Std::Parsers::StringParsers::_default::DigitNumber(), &({
                    Rc::new(move |previous: &nat,c: &nat| -> nat{
            {
                let __pat_let7_0: DafnyInt = previous.clone() * int!(10) + c.clone();
                {
                    let r: nat = __pat_let7_0.clone();
                    r.clone()
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                }), result)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(9383,3)
                pub fn Int() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<DafnyInt>>> {
                    crate::Std::Parsers::StringParsers::_default::Bind::<Rc<Option<DafnyChar>>, DafnyInt>(&crate::Std::Parsers::StringParsers::_default::Maybe::<DafnyChar>(&crate::Std::Parsers::StringParsers::_default::Char(&DafnyChar(char::from_u32(45).unwrap()))), &({
                            Rc::new(move |minusSign: &Rc<Option<DafnyChar>>| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<DafnyInt>>>{
            crate::Std::Parsers::StringParsers::_default::Map::<nat, DafnyInt>(&crate::Std::Parsers::StringParsers::_default::Nat(), {
                    let minusSign: Rc<Option<DafnyChar>> = minusSign.clone();
                    &({
                        let mut minusSign = minusSign.clone();
                        Rc::new(move |result: &nat| -> DafnyInt{
            if matches!((&minusSign).as_ref(), Some{ .. }) {
                int!(0) - result.clone()
            } else {
                result.clone()
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                    })
                })
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(9388,3)
                pub fn String(expected: &Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Sequence<DafnyChar>>>> {
                    {
                        let expected: Sequence<DafnyChar> = expected.clone();
                        {
                            let mut expected = expected.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Sequence<DafnyChar>>>{
            if !(crate::Std::Parsers::InputString::_default::Length(input) < expected.cardinality()) && Slice::<DafnyChar>::View(AsRef::as_ref(&crate::Std::Parsers::InputString::_default::Slice(input, &int!(0), &expected.cardinality()))) == expected.clone() {
                Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<Sequence<DafnyChar>> {
                        result: expected.clone(),
                        remaining: crate::Std::Parsers::InputString::_default::Drop(input, &expected.cardinality())
                    })
            } else {
                Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<Sequence<DafnyChar>> {
                        level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}),
                        data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                    message: string_of("expected '").concat(&expected).concat(&string_of("'")),
                                    remaining: input.clone(),
                                    next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                })
                    })
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9432,3)
                pub fn ExtractLineCol(input: &Sequence<DafnyChar>, pos: &nat) -> Rc<crate::Std::Parsers::StringParsers::CodeLocation> {
                    let mut output = MaybePlacebo::<Rc<crate::Std::Parsers::StringParsers::CodeLocation>>::new();
                    let mut lineNumber: DafnyInt;
                    let mut colNumber: DafnyInt;
                    let mut lineStr = MaybePlacebo::<Sequence<DafnyChar>>::new();
                    lineNumber = int!(1);
                    let mut startLinePos: nat = int!(0);
                    colNumber = int!(0);
                    let mut i: DafnyInt = int!(0);
                    while i.clone() < input.cardinality() && !(i.clone() == pos.clone()) {
                        colNumber = colNumber.clone() + int!(1);
                        if input.get(&i) == DafnyChar(char::from_u32(13).unwrap()) && i.clone() + int!(1) < input.cardinality() && input.get(&(i.clone() + int!(1))) == DafnyChar(char::from_u32(10).unwrap()) {
                            lineNumber = lineNumber.clone() + int!(1);
                            colNumber = int!(0);
                            i = i.clone() + int!(1);
                            startLinePos = i.clone() + int!(1);
                        } else {
                            if string_of("\r\n").contains(&input.get(&i)) {
                                lineNumber = lineNumber.clone() + int!(1);
                                colNumber = int!(0);
                                startLinePos = i.clone() + int!(1);
                            }
                        };
                        i = i.clone() + int!(1);
                    };
                    while i.clone() < input.cardinality() && !string_of("\r\n").contains(&input.get(&i)) {
                        i = i.clone() + int!(1);
                    };
                    lineStr = MaybePlacebo::from(input.slice(&startLinePos, &i));
                    output = MaybePlacebo::from(Rc::new(crate::Std::Parsers::StringParsers::CodeLocation::CodeLocation {
                                    lineNumber: lineNumber.clone(),
                                    colNumber: colNumber.clone(),
                                    lineStr: lineStr.read()
                                }));
                    return output.read();
                }
                /// DafnyStandardLibraries-rs.dfy(9492,3)
                pub fn DebugSummary(input: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                    (if int!(0) < input.cardinality() {
                        string_of("'").concat(&(if input.get(&int!(0)) == DafnyChar(char::from_u32(10).unwrap()) {
                                string_of("\\n")
                            } else {
                                if input.get(&int!(0)) == DafnyChar(char::from_u32(13).unwrap()) {
                                    string_of("\\r")
                                } else {
                                    if input.get(&int!(0)) == DafnyChar(char::from_u32(9).unwrap()) {
                                        string_of("\\t")
                                    } else {
                                        {
                                            let __pat_let8_0: DafnyChar = input.get(&int!(0));
                                            {
                                                let c: DafnyChar = __pat_let8_0.clone();
                                                seq![c.clone()]
                                            }
                                        }
                                    }
                                }
                            })).concat(&(if input.cardinality() == int!(1) {
                                string_of("' and end of string")
                            } else {
                                string_of("'").concat(&string_of(" and ")).concat(&crate::Std::Strings::_default::OfInt(&(input.cardinality() - int!(1)))).concat(&string_of(" char")).concat(&(if input.cardinality() == int!(2) {
                                        string_of("")
                                    } else {
                                        string_of("s")
                                    })).concat(&string_of(" remaining"))
                            }))
                    } else {
                        string_of("'' (end of string)")
                    }).concat(&string_of("\n"))
                }
                /// DafnyStandardLibraries-rs.dfy(9497,3)
                pub fn DebugNameSummary(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                    string_of("[").concat(name).concat(&string_of("] ")).concat(&crate::Std::Parsers::StringParsers::_default::DebugSummary(input))
                }
                /// DafnyStandardLibraries-rs.dfy(9502,3)
                pub fn DebugSummaryInput(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                    string_of("> ").concat(&crate::Std::Parsers::StringParsers::_default::DebugNameSummary(name, input))
                }
                /// DafnyStandardLibraries-rs.dfy(9507,3)
                pub fn PrintDebugSummaryInput(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>) -> () {
                    print!("{}", DafnyPrintWrapper(&crate::Std::Parsers::StringParsers::_default::DebugSummaryInput(name, input)));
                    return ();
                }
                /// DafnyStandardLibraries-rs.dfy(9512,3)
                pub fn NewIndent(input: &Sequence<DafnyChar>, indent: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                    let mut _accumulator: Sequence<DafnyChar> = seq![] as Sequence<DafnyChar>;
                    let mut _r0 = input.clone();
                    let mut _r1 = indent.clone();
                    'TAIL_CALL_START: loop {
                        let input = _r0;
                        let indent = _r1;
                        if input.cardinality() == int!(0) {
                            return _accumulator.concat(&string_of(""));
                        } else {
                            _accumulator = _accumulator.concat(&(if input.get(&int!(0)) == DafnyChar(char::from_u32(10).unwrap()) {
                                        input.take(&int!(1)).concat(&indent)
                                    } else {
                                        input.take(&int!(1))
                                    }));
                            let mut _in0: Sequence<DafnyChar> = input.drop(&int!(1));
                            let mut _in1: Sequence<DafnyChar> = indent.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9520,3)
                pub fn PrintDebugSummaryOutput<_R: DafnyType>(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>, result: &Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>) -> () {
                    print!("{}", DafnyPrintWrapper(&string_of("< ")));
                    print!("{}", DafnyPrintWrapper(&crate::Std::Parsers::StringParsers::_default::DebugNameSummary(name, input)));
                    if matches!(result.as_ref(), ParseFailure{ .. }) {
                        print!("{}", DafnyPrintWrapper(&string_of("| Unparsed: ")));
                        print!("{}", DafnyPrintWrapper(&crate::Std::Parsers::StringParsers::_default::DebugSummary(&crate::Std::Parsers::InputString::_default::View(&result.Remaining()))));
                        if crate::Std::Parsers::InputString::_default::Length(&result.Remaining()) < input.cardinality() {
                            print!("{}", DafnyPrintWrapper(&string_of("| Was committed\n")))
                        };
                        print!("{}", DafnyPrintWrapper(&string_of("| ").concat(&crate::Std::Parsers::StringParsers::_default::NewIndent(&crate::Std::Parsers::StringParsers::_default::FailureToString::<_R>(input, result, &int!(-1)), &string_of("| ")))));
                        print!("{}", DafnyPrintWrapper(&string_of("\n")))
                    } else {
                        print!("{}", DafnyPrintWrapper(&string_of("| Success: ")));
                        print!("{}", DafnyPrintWrapper(result.result()));
                        print!("{}", DafnyPrintWrapper(&string_of(", ")));
                        print!("{}", DafnyPrintWrapper(&crate::Std::Parsers::StringParsers::_default::DebugSummary(&crate::Std::Parsers::InputString::_default::View(&result.Remaining()))));
                        print!("{}", DafnyPrintWrapper(&string_of("\n")))
                    };
                    return ();
                }
                /// DafnyStandardLibraries-rs.dfy(9534,3)
                pub fn FailureToString<_R: DafnyType>(input: &Sequence<DafnyChar>, result: &Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>, printPos: &DafnyInt) -> Sequence<DafnyChar> {
                    let mut failure: Sequence<DafnyChar> = string_of("");
                    let mut failure: Sequence<DafnyChar> = failure.concat(&(if printPos.clone() == int!(-1) {
                                (if result.level().clone() == Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {}) {
                                    string_of("Fatal error")
                                } else {
                                    string_of("Error")
                                }).concat(&string_of(":\n"))
                            } else {
                                string_of("")
                            }));
                    let mut pos: DafnyInt = input.cardinality() - crate::Std::Parsers::InputString::_default::Length(result.data().remaining());
                    let mut pos: DafnyInt = if pos.clone() < int!(0) {
                            int!(0)
                        } else {
                            pos.clone()
                        };
                    let mut failure: Sequence<DafnyChar> = if printPos.clone() == pos.clone() {
                            failure.clone()
                        } else {
                            {
                                let __pat_let9_0: Rc<crate::Std::Parsers::StringParsers::CodeLocation> = crate::Std::Parsers::StringParsers::_default::ExtractLineCol(input, &pos);
                                {
                                    let output: Rc<crate::Std::Parsers::StringParsers::CodeLocation> = __pat_let9_0.clone();
                                    {
                                        let __pat_let10_0: Rc<crate::Std::Parsers::StringParsers::CodeLocation> = output.clone();
                                        {
                                            let line: nat = __pat_let10_0.lineNumber().clone();
                                            {
                                                let col: nat = __pat_let10_0.colNumber().clone();
                                                {
                                                    let lineStr: Sequence<DafnyChar> = __pat_let10_0.lineStr().clone();
                                                    failure.concat(&crate::Std::Strings::_default::OfInt(&line)).concat(&string_of(": ")).concat(&lineStr).concat(&string_of("\n")).concat(&crate::Std::Collections::Seq::_default::Repeat::<DafnyChar>(&DafnyChar(char::from_u32(32).unwrap()), &(col.clone() + int!(2) + crate::Std::Strings::_default::OfInt(&line).cardinality()))).concat(&string_of("^")).concat(&string_of("\n"))
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        };
                    let mut failure: Sequence<DafnyChar> = failure.concat(result.data().message());
                    if matches!(result.data().next().as_ref(), Some{ .. }) {
                        let mut failure: Sequence<DafnyChar> = failure.concat(&string_of(", or\n"));
                        let mut subFailure: Sequence<DafnyChar> = crate::Std::Parsers::StringParsers::_default::FailureToString::<_R>(input, &Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_R> {
                                        level: result.level().clone(),
                                        data: result.data().next().value().clone()
                                    }), &pos);
                        let mut failure: Sequence<DafnyChar> = failure.concat(&subFailure);
                        failure.clone()
                    } else {
                        let mut failure: Sequence<DafnyChar> = failure.concat(&string_of("\n"));
                        failure.clone()
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9553,3)
                pub fn Apply<_T: DafnyType>(parser: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_T>>>, input: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_T>> {
                    parser(&crate::Std::Parsers::StringParsers::_default::ToInput(input))
                }
                /// DafnyStandardLibraries-rs.dfy(9558,3)
                pub fn ToInput(input: &Sequence<DafnyChar>) -> Input {
                    Rc::new(Slice::Slice::<DafnyChar> {
                            data: input.clone(),
                            start: int!(0),
                            end: input.cardinality()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8518,3)
                pub fn IsRemaining(input: &Input, remaining: &Input) -> bool {
                    !(crate::Std::Parsers::InputString::_default::Length(input) < crate::Std::Parsers::InputString::_default::Length(remaining)) && crate::Std::Parsers::InputString::_default::Drop(input, &(crate::Std::Parsers::InputString::_default::Length(input) - crate::Std::Parsers::InputString::_default::Length(remaining))) == remaining.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(8532,3)
                pub fn SucceedWith<_R: DafnyType>(result: &_R) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let result: _R = result.clone();
                        {
                            let mut result = result.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<_R> {
                    result: result.clone(),
                    remaining: input.clone()
                })
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8537,3)
                pub fn Epsilon() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<()>>> {
                    crate::Std::Parsers::StringParsers::_default::SucceedWith::<()>(&(()))
                }
                /// DafnyStandardLibraries-rs.dfy(8542,3)
                pub fn FailWith<_R: DafnyType>(message: &Sequence<DafnyChar>, level: &Rc<crate::Std::Parsers::StringParsers::FailureLevel>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let level: Rc<crate::Std::Parsers::StringParsers::FailureLevel> = level.clone();
                        let message: Sequence<DafnyChar> = message.clone();
                        {
                            let mut level = level.clone();
                            let mut message = message.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_R> {
                    level: level.clone(),
                    data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                message: message.clone(),
                                remaining: input.clone(),
                                next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                            })
                })
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8547,3)
                pub fn ResultWith<_R: DafnyType>(result: &Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let result: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = result.clone();
                        {
                            let mut result = result.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            result.clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8552,3)
                pub fn EndOfString() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<()>>> {
                    {
                        Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<()>>{
            if crate::Std::Parsers::InputString::_default::Length(input) == int!(0) {
                Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<()> {
                        result: (),
                        remaining: input.clone()
                    })
            } else {
                Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<()> {
                        level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}),
                        data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                    message: string_of("expected end of string"),
                                    remaining: input.clone(),
                                    next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                })
                    })
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8557,3)
                pub fn Bind<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&_L) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&_L) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let11_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let11_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<_R>()
                    } else {
                        {
                            let __pat_let12_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let leftResult: _L = __pat_let12_0.0.clone();
                                {
                                    let remaining: Input = __pat_let12_0.1.clone();
                                    (&(&right)(&leftResult))(&remaining)
                                }
                            }
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8562,3)
                pub fn BindSucceeds<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&_L, &Input) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&_L, &Input) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let13_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let13_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<_R>()
                    } else {
                        {
                            let __pat_let14_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let leftResult: _L = __pat_let14_0.0.clone();
                                {
                                    let remaining: Input = __pat_let14_0.1.clone();
                                    (&(&right)(&leftResult, &remaining))(&remaining)
                                }
                            }
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8567,3)
                pub fn BindResult<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>, &Input) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let right: Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>, &Input) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = right.clone();
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            (&(&right)(&(&left)(input), input))(input)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8572,3)
                pub fn Map<_R: DafnyType, _U: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>, mappingFunc: &Rc<dyn ::std::ops::Fn(&_R) -> _U>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_U>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        let mappingFunc: Rc<dyn ::std::ops::Fn(&_R) -> _U> = mappingFunc.clone();
                        {
                            let mut underlying = underlying.clone();
                            let mut mappingFunc = mappingFunc.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_U>>{
            {
                let __pat_let15_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let15_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<_U>()
                    } else {
                        {
                            let __pat_let16_0: (_R, Input) = valueOrError0.Extract();
                            {
                                let result: _R = __pat_let16_0.0.clone();
                                {
                                    let remaining: Input = __pat_let16_0.1.clone();
                                    {
                                        let __pat_let17_0: _U = (&mappingFunc)(&result);
                                        {
                                            let u: _U = __pat_let17_0.clone();
                                            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<_U> {
                                                    result: u.clone(),
                                                    remaining: remaining.clone()
                                                })
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8577,3)
                pub fn Not<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<()>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        {
                            let mut underlying = underlying.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<()>>{
            {
                let __pat_let18_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                {
                    let l: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let18_0.clone();
                    if l.IsFailure() {
                        if l.IsFatal() {
                            l.PropagateFailure::<()>()
                        } else {
                            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<()> {
                                    result: (),
                                    remaining: input.clone()
                                })
                        }
                    } else {
                        Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<()> {
                                level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}),
                                data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                            message: string_of("not failed"),
                                            remaining: input.clone(),
                                            next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                        })
                            })
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8582,3)
                pub fn And<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<(_L, _R)>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<(_L, _R)>>{
            {
                let __pat_let19_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let19_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<(_L, _R)>()
                    } else {
                        {
                            let __pat_let20_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let l: _L = __pat_let20_0.0.clone();
                                {
                                    let remainingLeft: Input = __pat_let20_0.1.clone();
                                    {
                                        let __pat_let21_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&right)(input);
                                        {
                                            let valueOrError1: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let21_0.clone();
                                            if valueOrError1.IsFailure() {
                                                valueOrError1.PropagateFailure::<(_L, _R)>()
                                            } else {
                                                {
                                                    let __pat_let22_0: (_R, Input) = valueOrError1.Extract();
                                                    {
                                                        let r: _R = __pat_let22_0.0.clone();
                                                        {
                                                            let remainingRight: Input = __pat_let22_0.1.clone();
                                                            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<(_L, _R)> {
                                                                    result: (
                                                                            l.clone(),
                                                                            r.clone()
                                                                        ),
                                                                    remaining: remainingRight.clone()
                                                                })
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8587,3)
                pub fn Or<_R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let23_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&left)(input);
                {
                    let p: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let23_0.clone();
                    if !p.NeedsAlternative(input) {
                        p.clone()
                    } else {
                        {
                            let __pat_let24_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&right)(input);
                            {
                                let p2: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let24_0.clone();
                                if !p2.NeedsAlternative(input) {
                                    p2.clone()
                                } else {
                                    p2.MapRecoverableError({
                                            let p: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = p.clone();
                                            &({
                                                let mut p = p.clone();
                                                Rc::new(move |dataRight: &Rc<crate::Std::Parsers::StringParsers::FailureData>| -> Rc<crate::Std::Parsers::StringParsers::FailureData>{
            p.data().Concat(dataRight)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                            })
                                        })
                                }
                            }
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8592,3)
                pub fn OrSeq<_R: DafnyType>(alternatives: &Sequence<Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    if alternatives.cardinality() == int!(0) {
                        crate::Std::Parsers::StringParsers::_default::FailWith::<_R>(&string_of("no alternatives"), &Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}))
                    } else {
                        if alternatives.cardinality() == int!(1) {
                            alternatives.get(&int!(0))
                        } else {
                            crate::Std::Parsers::StringParsers::_default::Or::<_R>(&alternatives.get(&int!(0)), &crate::Std::Parsers::StringParsers::_default::OrSeq::<_R>(&alternatives.drop(&int!(1))))
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8602,3)
                pub fn Lookahead<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        {
                            let mut underlying = underlying.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let25_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                {
                    let p: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let25_0.clone();
                    if p.IsFailure() {
                        if p.IsFatal() {
                            p.clone()
                        } else {
                            {
                                let __pat_let26_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = p.clone();
                                {
                                    let _dt__update__tmp_h0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let26_0.clone();
                                    {
                                        let __pat_let27_0: Rc<crate::Std::Parsers::StringParsers::FailureData> = Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                                    message: p.data().message().clone(),
                                                    remaining: input.clone(),
                                                    next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                                });
                                        {
                                            let _dt__update_hdata_h0: Rc<crate::Std::Parsers::StringParsers::FailureData> = __pat_let27_0.clone();
                                            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_R> {
                                                    level: _dt__update__tmp_h0.level().clone(),
                                                    data: _dt__update_hdata_h0.clone()
                                                })
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        {
                            let __pat_let28_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = p.clone();
                            {
                                let _dt__update__tmp_h1: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let28_0.clone();
                                {
                                    let __pat_let29_0: Input = input.clone();
                                    {
                                        let _dt__update_hremaining_h0: Input = __pat_let29_0.clone();
                                        Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<_R> {
                                                result: _dt__update__tmp_h1.result().clone(),
                                                remaining: _dt__update_hremaining_h0.clone()
                                            })
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8607,3)
                pub fn _q<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        {
                            let mut underlying = underlying.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let30_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                {
                    let p: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let30_0.clone();
                    if p.IsFailure() {
                        if p.IsFatal() {
                            p.clone()
                        } else {
                            {
                                let __pat_let31_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = p.clone();
                                {
                                    let _dt__update__tmp_h0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let31_0.clone();
                                    {
                                        let __pat_let32_0: Rc<crate::Std::Parsers::StringParsers::FailureData> = Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                                    message: p.data().message().clone(),
                                                    remaining: input.clone(),
                                                    next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                                });
                                        {
                                            let _dt__update_hdata_h0: Rc<crate::Std::Parsers::StringParsers::FailureData> = __pat_let32_0.clone();
                                            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_R> {
                                                    level: _dt__update__tmp_h0.level().clone(),
                                                    data: _dt__update_hdata_h0.clone()
                                                })
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        p.clone()
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8612,3)
                pub fn If<_L: DafnyType, _R: DafnyType>(condition: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, succeed: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    crate::Std::Parsers::StringParsers::_default::Bind::<_L, _R>(&crate::Std::Parsers::StringParsers::_default::Lookahead::<_L>(condition), {
                            let succeed: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = succeed.clone();
                            &({
                                let mut succeed = succeed.clone();
                                Rc::new(move |l: &_L| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>{
            succeed.clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8629,3)
                pub fn Maybe<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<Option<_R>>>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        {
                            let mut underlying = underlying.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<Option<_R>>>>{
            {
                let __pat_let33_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                {
                    let u: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let33_0.clone();
                    if u.IsFatalFailure() || u.IsFailure() && !u.NeedsAlternative(input) {
                        u.PropagateFailure::<Rc<Option<_R>>>()
                    } else {
                        if matches!((&u).as_ref(), ParseSuccess{ .. }) {
                            u.Map::<Rc<Option<_R>>>(&({
                                    Rc::new(move |result: &_R| -> Rc<Option<_R>>{
            Rc::new(Option::Some::<_R> {
                    value: result.clone()
                })
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                }))
                        } else {
                            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<Rc<Option<_R>>> {
                                    result: Rc::new(Option::None::<_R> {}),
                                    remaining: input.clone()
                                })
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8634,3)
                pub fn ConcatMap<_L: DafnyType, _R: DafnyType, _T: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>, mapper: &Rc<dyn ::std::ops::Fn(&_L, &_R) -> _T>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_T>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = right.clone();
                        let mapper: Rc<dyn ::std::ops::Fn(&_L, &_R) -> _T> = mapper.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            let mut mapper = mapper.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_T>>{
            {
                let __pat_let34_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let34_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<_T>()
                    } else {
                        {
                            let __pat_let35_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let l: _L = __pat_let35_0.0.clone();
                                {
                                    let remaining: Input = __pat_let35_0.1.clone();
                                    {
                                        let __pat_let36_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&right)(&remaining);
                                        {
                                            let valueOrError1: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let36_0.clone();
                                            if valueOrError1.IsFailure() {
                                                valueOrError1.PropagateFailure::<_T>()
                                            } else {
                                                {
                                                    let __pat_let37_0: (_R, Input) = valueOrError1.Extract();
                                                    {
                                                        let r: _R = __pat_let37_0.0.clone();
                                                        {
                                                            let remaining2: Input = __pat_let37_0.1.clone();
                                                            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<_T> {
                                                                    result: (&mapper)(&l, &r),
                                                                    remaining: remaining2.clone()
                                                                })
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8639,3)
                pub fn Concat<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<(_L, _R)>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<(_L, _R)>>{
            {
                let __pat_let38_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let38_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<(_L, _R)>()
                    } else {
                        {
                            let __pat_let39_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let l: _L = __pat_let39_0.0.clone();
                                {
                                    let remaining: Input = __pat_let39_0.1.clone();
                                    {
                                        let __pat_let40_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&right)(&remaining);
                                        {
                                            let valueOrError1: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let40_0.clone();
                                            if valueOrError1.IsFailure() {
                                                valueOrError1.PropagateFailure::<(_L, _R)>()
                                            } else {
                                                {
                                                    let __pat_let41_0: (_R, Input) = valueOrError1.Extract();
                                                    {
                                                        let r: _R = __pat_let41_0.0.clone();
                                                        {
                                                            let remaining2: Input = __pat_let41_0.1.clone();
                                                            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<(_L, _R)> {
                                                                    result: (
                                                                            l.clone(),
                                                                            r.clone()
                                                                        ),
                                                                    remaining: remaining2.clone()
                                                                })
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8644,3)
                pub fn ConcatKeepRight<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    crate::Std::Parsers::StringParsers::_default::ConcatMap::<_L, _R, _R>(left, right, &({
                            Rc::new(move |l: &_L,r: &_R| -> _R{
            r.clone()
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(8649,3)
                pub fn ConcatKeepLeft<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> {
                    crate::Std::Parsers::StringParsers::_default::ConcatMap::<_L, _R, _L>(left, right, &({
                            Rc::new(move |l: &_L,r: &_R| -> _L{
            l.clone()
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(8654,3)
                pub fn Debug<_R: DafnyType, _D: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>, name: &Sequence<DafnyChar>, onEnter: &Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>, &Input) -> _D>, onExit: &Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>, &_D, &Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>) -> ()>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let onEnter: Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>, &Input) -> _D> = onEnter.clone();
                        let name: Sequence<DafnyChar> = name.clone();
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        let onExit: Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>, &_D, &Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>) -> ()> = onExit.clone();
                        {
                            let mut underlying = underlying.clone();
                            let mut name = name.clone();
                            let mut onExit = onExit.clone();
                            let mut onEnter = onEnter.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let42_0: _D = (&onEnter)(&name, input);
                {
                    let debugData: _D = __pat_let42_0.clone();
                    {
                        let __pat_let43_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                        {
                            let output: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let43_0.clone();
                            {
                                let __pat_let44_0: () = (&onExit)(&name, &debugData, &output);
                                {
                                    let _v1: () = __pat_let44_0.clone();
                                    output.clone()
                                }
                            }
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8659,3)
                pub fn ZeroOrMore<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Sequence<_R>>>> {
                    crate::Std::Parsers::StringParsers::_default::Map::<Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>, Sequence<_R>>(&crate::Std::Parsers::StringParsers::_default::Rep::<Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>, _R>(underlying, &({
                                Rc::new(move |result: &Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>,r: &_R| -> Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>{
            result.Append(r)
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                            }), &Rc::new(crate::Std::Parsers::StringParsers::SeqB::SeqBNil::<_R> {})), &({
                            Rc::new(move |result: &Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>| -> Sequence<_R>{
            result.ToSequence()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(8664,3)
                pub fn OneOrMore<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Sequence<_R>>>> {
                    crate::Std::Parsers::StringParsers::_default::Bind::<_R, Sequence<_R>>(underlying, {
                            let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                            &({
                                let mut underlying = underlying.clone();
                                Rc::new(move |r: &_R| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Sequence<_R>>>>{
            crate::Std::Parsers::StringParsers::_default::Map::<Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>, Sequence<_R>>(&crate::Std::Parsers::StringParsers::_default::Rep::<Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>, _R>(&underlying, &({
                        Rc::new(move |result: &Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>,r: &_R| -> Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>{
            result.Append(r)
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                    }), &Rc::new(crate::Std::Parsers::StringParsers::SeqB::SeqBCons::<_R> {
                            last: r.clone(),
                            init: Rc::new(crate::Std::Parsers::StringParsers::SeqB::SeqBNil::<_R> {})
                        })), &({
                    Rc::new(move |result: &Rc<crate::Std::Parsers::StringParsers::SeqB<_R>>| -> Sequence<_R>{
            result.ToSequence()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                }))
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8669,3)
                pub fn Rep<_A: DafnyType, _B: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>>>, combine: &Rc<dyn ::std::ops::Fn(&_A, &_B) -> _A>, acc: &_A) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>>> = underlying.clone();
                        let combine: Rc<dyn ::std::ops::Fn(&_A, &_B) -> _A> = combine.clone();
                        let acc: _A = acc.clone();
                        {
                            let mut underlying = underlying.clone();
                            let mut acc = acc.clone();
                            let mut combine = combine.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>{
            crate::Std::Parsers::StringParsers::_default::Rep_::<_A, _B>(&underlying, &combine, &acc, input)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8674,3)
                pub fn RepSep<_A: DafnyType, _B: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>>, separator: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Sequence<_A>>>> {
                    crate::Std::Parsers::StringParsers::_default::Bind::<Rc<Option<_A>>, Sequence<_A>>(&crate::Std::Parsers::StringParsers::_default::Maybe::<_A>(underlying), {
                            let separator: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>>> = separator.clone();
                            let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>> = underlying.clone();
                            &({
                                let mut underlying = underlying.clone();
                                let mut separator = separator.clone();
                                Rc::new(move |result: &Rc<Option<_A>>| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Sequence<_A>>>>{
            if matches!(result.as_ref(), None{ .. }) {
                crate::Std::Parsers::StringParsers::_default::SucceedWith::<Sequence<_A>>(&(seq![] as Sequence<_A>))
            } else {
                crate::Std::Parsers::StringParsers::_default::Map::<Rc<crate::Std::Parsers::StringParsers::SeqB<_A>>, Sequence<_A>>(&crate::Std::Parsers::StringParsers::_default::Rep::<Rc<crate::Std::Parsers::StringParsers::SeqB<_A>>, _A>(&crate::Std::Parsers::StringParsers::_default::ConcatKeepRight::<_B, _A>(&separator, &underlying), &({
                            Rc::new(move |acc: &Rc<crate::Std::Parsers::StringParsers::SeqB<_A>>,a: &_A| -> Rc<crate::Std::Parsers::StringParsers::SeqB<_A>>{
            acc.Append(a)
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                        }), &Rc::new(crate::Std::Parsers::StringParsers::SeqB::SeqBCons::<_A> {
                                last: result.value().clone(),
                                init: Rc::new(crate::Std::Parsers::StringParsers::SeqB::SeqBNil::<_A> {})
                            })), &({
                        Rc::new(move |result: &Rc<crate::Std::Parsers::StringParsers::SeqB<_A>>| -> Sequence<_A>{
            result.ToSequence()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                    }))
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8679,3)
                pub fn RepMerge<_A: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>>, merger: &Rc<dyn ::std::ops::Fn(&_A, &_A) -> _A>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>> {
                    crate::Std::Parsers::StringParsers::_default::Bind::<Rc<Option<_A>>, _A>(&crate::Std::Parsers::StringParsers::_default::Maybe::<_A>(underlying), {
                            let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>> = underlying.clone();
                            let merger: Rc<dyn ::std::ops::Fn(&_A, &_A) -> _A> = merger.clone();
                            &({
                                let mut underlying = underlying.clone();
                                Rc::new(move |result: &Rc<Option<_A>>| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>>{
            if matches!(result.as_ref(), None{ .. }) {
                crate::Std::Parsers::StringParsers::_default::FailWith::<_A>(&string_of("No first element in RepMerge"), &Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}))
            } else {
                crate::Std::Parsers::StringParsers::_default::Rep::<_A, _A>(&underlying, {
                        let merger: Rc<dyn ::std::ops::Fn(&_A, &_A) -> _A> = merger.clone();
                        &({
                            let mut merger = merger.clone();
                            Rc::new(move |acc: &_A,a: &_A| -> _A{
            (&merger)(acc, a)
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                        })
                    }, result.value())
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8684,3)
                pub fn RepSepMerge<_A: DafnyType, _B: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>>, separator: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>>>, merger: &Rc<dyn ::std::ops::Fn(&_A, &_A) -> _A>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>> {
                    crate::Std::Parsers::StringParsers::_default::Bind::<Rc<Option<_A>>, _A>(&crate::Std::Parsers::StringParsers::_default::Maybe::<_A>(underlying), {
                            let separator: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>>> = separator.clone();
                            let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>> = underlying.clone();
                            let merger: Rc<dyn ::std::ops::Fn(&_A, &_A) -> _A> = merger.clone();
                            &({
                                let mut underlying = underlying.clone();
                                let mut separator = separator.clone();
                                Rc::new(move |result: &Rc<Option<_A>>| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>>>{
            if matches!(result.as_ref(), None{ .. }) {
                crate::Std::Parsers::StringParsers::_default::FailWith::<_A>(&string_of("No first element in RepSepMerge"), &Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}))
            } else {
                crate::Std::Parsers::StringParsers::_default::Rep::<_A, _A>(&crate::Std::Parsers::StringParsers::_default::ConcatKeepRight::<_B, _A>(&separator, &underlying), {
                        let merger: Rc<dyn ::std::ops::Fn(&_A, &_A) -> _A> = merger.clone();
                        &({
                            let mut merger = merger.clone();
                            Rc::new(move |acc: &_A,a: &_A| -> _A{
            (&merger)(acc, a)
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                        })
                    }, result.value())
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8689,3)
                pub fn Rep_<_A: DafnyType, _B: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>>>, combine: &Rc<dyn ::std::ops::Fn(&_A, &_B) -> _A>, acc: &_A, input: &Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_A>> {
                    let mut _r0 = underlying.clone();
                    let mut _r1 = combine.clone();
                    let mut _r2 = acc.clone();
                    let mut _r3 = input.clone();
                    'TAIL_CALL_START: loop {
                        let underlying = _r0;
                        let combine = _r1;
                        let acc = _r2;
                        let input = _r3;
                        let mut _source0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>> = (&underlying)(&input);
                        if matches!((&_source0).as_ref(), ParseFailure{ .. }) {
                            let mut ___mcc_h0: Rc<crate::Std::Parsers::StringParsers::FailureLevel> = _source0.level().clone();
                            let mut ___mcc_h1: Rc<crate::Std::Parsers::StringParsers::FailureData> = _source0.data().clone();
                            let mut failure: Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>> = (&underlying)(&input);
                            if failure.NeedsAlternative(&input) {
                                return Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<_A> {
                                            result: acc.clone(),
                                            remaining: input.clone()
                                        });
                            } else {
                                return failure.PropagateFailure::<_A>();
                            }
                        } else {
                            let mut ___mcc_h4: _B = _source0.result().clone();
                            let mut ___mcc_h5: Input = _source0.remaining().clone();
                            let mut remaining: Input = ___mcc_h5.clone();
                            let mut result: _B = ___mcc_h4.clone();
                            if !(crate::Std::Parsers::InputString::_default::Length(&remaining) < crate::Std::Parsers::InputString::_default::Length(&input)) {
                                return Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<_A> {
                                            result: acc.clone(),
                                            remaining: input.clone()
                                        });
                            } else {
                                let mut _in0: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_B>>> = underlying.clone();
                                let mut _in1: Rc<dyn ::std::ops::Fn(&_A, &_B) -> _A> = combine.clone();
                                let mut _in2: _A = (&combine)(&acc, &result);
                                let mut _in3: Input = remaining.clone();
                                _r0 = _in0.clone();
                                _r1 = _in1.clone();
                                _r2 = _in2.clone();
                                _r3 = _in3.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8705,3)
                pub fn Recursive<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = underlying.clone();
                        {
                            let mut underlying = underlying.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            crate::Std::Parsers::StringParsers::_default::Recursive_::<_R>(&underlying, input)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8710,3)
                pub fn RecursiveProgressError<_R: DafnyType>(name: &Sequence<DafnyChar>, input: &Input, remaining: &Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> {
                    if crate::Std::Parsers::InputString::_default::Length(remaining) == crate::Std::Parsers::InputString::_default::Length(input) {
                        Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_R> {
                                level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}),
                                data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                            message: name.concat(&string_of(" no progress in recursive parser")),
                                            remaining: remaining.clone(),
                                            next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                        })
                            })
                    } else {
                        Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_R> {
                                level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {}),
                                data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                            message: name.concat(&string_of("fixpoint called with an increasing remaining sequence")),
                                            remaining: remaining.clone(),
                                            next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                        })
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8720,3)
                pub fn Recursive_<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>, input: &Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> {
                    let mut callback: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = {
                            let input: Input = input.clone();
                            let underlying: Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = underlying.clone();
                            {
                                let mut underlying = underlying.clone();
                                let mut input = input.clone();
                                Rc::new(move |remaining: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            if crate::Std::Parsers::InputString::_default::Length(remaining) < crate::Std::Parsers::InputString::_default::Length(&input) {
                crate::Std::Parsers::StringParsers::_default::Recursive_::<_R>(&underlying, remaining)
            } else {
                crate::Std::Parsers::StringParsers::_default::RecursiveProgressError::<_R>(&string_of("Parsers.Recursive"), &input, remaining)
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        };
                    (&underlying(&callback))(input)
                }
                /// DafnyStandardLibraries-rs.dfy(8727,3)
                pub fn RecursiveNoStack<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>> = underlying.clone();
                        {
                            let mut underlying = underlying.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            crate::Std::Parsers::StringParsers::_default::RecursiveNoStack_::<_R>(&underlying, &underlying, input, &(seq![] as Sequence<Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>>>))
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8732,3)
                pub fn RecursiveNoStack_<_R: DafnyType>(continuation: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>, underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>, input: &Input, callbacks: &Sequence<Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>>>) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> {
                    let mut _r0 = continuation.clone();
                    let mut _r1 = underlying.clone();
                    let mut _r2 = input.clone();
                    let mut _r3 = callbacks.clone();
                    'TAIL_CALL_START: loop {
                        let continuation = _r0;
                        let underlying = _r1;
                        let input = _r2;
                        let callbacks = _r3;
                        let mut valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>> = (&continuation)(&input);
                        if valueOrError0.IsFailure() {
                            return valueOrError0.PropagateFailure::<_R>();
                        } else {
                            let mut __let_tmp_rhs0: (Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>, Input) = valueOrError0.Extract();
                            let mut recursor: Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>> = __let_tmp_rhs0.0.clone();
                            let mut remaining: Input = __let_tmp_rhs0.1.clone();
                            let mut _source0: Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>> = recursor.clone();
                            if matches!((&_source0).as_ref(), RecursiveReturn{ .. }) {
                                let mut ___mcc_h0: _R = _source0._h4().clone();
                                let mut result: _R = ___mcc_h0.clone();
                                if callbacks.cardinality() == int!(0) {
                                    return Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<_R> {
                                                result: result.clone(),
                                                remaining: remaining.clone()
                                            });
                                } else {
                                    let mut toCompute: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>> = (&callbacks.get(&int!(0)))(&Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<_R> {
                                                    result: result.clone(),
                                                    remaining: remaining.clone()
                                                }));
                                    if crate::Std::Parsers::InputString::_default::Length(&input) < crate::Std::Parsers::InputString::_default::Length(&remaining) {
                                        return crate::Std::Parsers::StringParsers::_default::RecursiveProgressError::<_R>(&string_of("Parsers.RecursiveNoStack[internal]"), &input, &remaining);
                                    } else {
                                        let mut _in0: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>> = toCompute.clone();
                                        let mut _in1: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>> = underlying.clone();
                                        let mut _in2: Input = remaining.clone();
                                        let mut _in3: Sequence<Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>>> = callbacks.drop(&int!(1));
                                        _r0 = _in0.clone();
                                        _r1 = _in1.clone();
                                        _r2 = _in2.clone();
                                        _r3 = _in3.clone();
                                        continue 'TAIL_CALL_START;
                                    }
                                }
                            } else {
                                let mut ___mcc_h1: Rc<dyn ::std::ops::Fn(&_R) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>> = _source0._h5().clone();
                                let mut rToNewParserOfRecursiveNoStackResultOfR: Rc<dyn ::std::ops::Fn(&_R) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>> = ___mcc_h1.clone();
                                if !(crate::Std::Parsers::InputString::_default::Length(&remaining) < crate::Std::Parsers::InputString::_default::Length(&input)) {
                                    return crate::Std::Parsers::StringParsers::_default::RecursiveProgressError::<_R>(&string_of("Parsers.RecursiveNoStack"), &input, &remaining);
                                } else {
                                    let mut _in4: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>> = underlying.clone();
                                    let mut _in5: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>> = underlying.clone();
                                    let mut _in6: Input = remaining.clone();
                                    let mut _in7: Sequence<Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>>> = seq![{
                                                let rToNewParserOfRecursiveNoStackResultOfR: Rc<dyn ::std::ops::Fn(&_R) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>> = rToNewParserOfRecursiveNoStackResultOfR.clone();
                                                {
                                                    let mut rToNewParserOfRecursiveNoStackResultOfR = rToNewParserOfRecursiveNoStackResultOfR.clone();
                                                    Rc::new(move |p: &Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>| -> Rc<dyn ::std::ops::Fn(&Rc<Slice<DafnyChar>>) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>{
            if p.IsFailure() {
                crate::Std::Parsers::StringParsers::_default::ResultWith::<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>(&p.PropagateFailure::<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>())
            } else {
                {
                    let __pat_let45_0: (_R, Input) = p.Extract();
                    {
                        let r: _R = __pat_let45_0.0.clone();
                        {
                            let remaining2: Input = __pat_let45_0.1.clone();
                            (&rToNewParserOfRecursiveNoStackResultOfR)(&r)
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                                }
                                            }].concat(&callbacks);
                                    _r0 = _in4.clone();
                                    _r1 = _in5.clone();
                                    _r2 = _in6.clone();
                                    _r3 = _in7.clone();
                                    continue 'TAIL_CALL_START;
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8738,3)
                pub fn RecursiveMap<_R: DafnyType>(underlying: &Map<Sequence<DafnyChar>, Rc<crate::Std::Parsers::StringParsers::RecursiveDef<_R>>>, fun: &Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let underlying: Map<Sequence<DafnyChar>, Rc<crate::Std::Parsers::StringParsers::RecursiveDef<_R>>> = underlying.clone();
                        let fun: Sequence<DafnyChar> = fun.clone();
                        {
                            let mut underlying = underlying.clone();
                            let mut fun = fun.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            crate::Std::Parsers::StringParsers::_default::RecursiveMap_::<_R>(&underlying, &fun, input)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8743,3)
                pub fn RecursiveMap_<_R: DafnyType>(underlying: &Map<Sequence<DafnyChar>, Rc<crate::Std::Parsers::StringParsers::RecursiveDef<_R>>>, fun: &Sequence<DafnyChar>, input: &Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> {
                    if !underlying.contains(fun) {
                        Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_R> {
                                level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {}),
                                data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                            message: string_of("parser '").concat(fun).concat(&string_of("' not found")),
                                            remaining: input.clone(),
                                            next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                        })
                            })
                    } else {
                        let mut __let_tmp_rhs0: Rc<crate::Std::Parsers::StringParsers::RecursiveDef<_R>> = underlying.get(fun);
                        let mut orderFun: nat = __let_tmp_rhs0.order().clone();
                        let mut definitionFun: Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = __let_tmp_rhs0.definition().clone();
                        let mut callback: Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = {
                                let underlying: Map<Sequence<DafnyChar>, Rc<crate::Std::Parsers::StringParsers::RecursiveDef<_R>>> = underlying.clone();
                                let input: Input = input.clone();
                                let orderFun: nat = orderFun.clone();
                                let fun: Sequence<DafnyChar> = fun.clone();
                                {
                                    let mut underlying = underlying.clone();
                                    Rc::new(move |_fun_k: &Sequence<DafnyChar>| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>{
            {
                let __pat_let46_0: Rc<dyn ::std::ops::Fn(&Rc<Slice<DafnyChar>>) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = if !underlying.keys().contains(_fun_k) {
                        crate::Std::Parsers::StringParsers::_default::FailWith::<_R>(&_fun_k.concat(&string_of(" not defined")), &Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {}))
                    } else {
                        {
                            let __pat_let47_0: Rc<crate::Std::Parsers::StringParsers::RecursiveDef<_R>> = underlying.get(_fun_k);
                            {
                                let _orderFun_k: nat = __pat_let47_0.order().clone();
                                {
                                    let _definitionFun_k: Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = __pat_let47_0.definition().clone();
                                    {
                                        let input: Input = input.clone();
                                        let _orderFun_k: nat = _orderFun_k.clone();
                                        let orderFun: nat = orderFun.clone();
                                        let underlying: Map<Sequence<DafnyChar>, Rc<crate::Std::Parsers::StringParsers::RecursiveDef<_R>>> = underlying.clone();
                                        let _fun_k: Sequence<DafnyChar> = _fun_k.clone();
                                        let fun: Sequence<DafnyChar> = fun.clone();
                                        {
                                            let mut underlying = underlying.clone();
                                            let mut _orderFun_k = _orderFun_k.clone();
                                            let mut fun = fun.clone();
                                            let mut input = input.clone();
                                            let mut _fun_k = _fun_k.clone();
                                            let mut orderFun = orderFun.clone();
                                            Rc::new(move |remaining: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            if crate::Std::Parsers::InputString::_default::Length(remaining) < crate::Std::Parsers::InputString::_default::Length(&input) || crate::Std::Parsers::InputString::_default::Length(remaining) == crate::Std::Parsers::InputString::_default::Length(&input) && _orderFun_k.clone() < orderFun.clone() {
                crate::Std::Parsers::StringParsers::_default::RecursiveMap_::<_R>(&underlying, &_fun_k, remaining)
            } else {
                if crate::Std::Parsers::InputString::_default::Length(remaining) == crate::Std::Parsers::InputString::_default::Length(&input) {
                    Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_R> {
                            level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}),
                            data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                        message: string_of("non-progressing recursive call requires that order of '").concat(&_fun_k).concat(&string_of("' (")).concat(&crate::Std::Strings::_default::OfInt(&_orderFun_k)).concat(&string_of(") is lower than the order of '")).concat(&fun).concat(&string_of("' (")).concat(&crate::Std::Strings::_default::OfInt(&orderFun)).concat(&string_of(")")),
                                        remaining: remaining.clone(),
                                        next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                    })
                        })
                } else {
                    Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_R> {
                            level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {}),
                            data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                        message: string_of("parser did not return a suffix of the input"),
                                        remaining: remaining.clone(),
                                        next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                    })
                        })
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }
                                    }
                                }
                            }
                        }
                    };
                {
                    let p: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = __pat_let46_0.clone();
                    p.clone()
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                }
                            };
                        (&(&definitionFun)(&callback))(input)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8752,3)
                pub fn CharTest(test: &Rc<dyn ::std::ops::Fn(&DafnyChar) -> bool>, name: &Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<DafnyChar>>> {
                    {
                        let test: Rc<dyn ::std::ops::Fn(&DafnyChar) -> bool> = test.clone();
                        let name: Sequence<DafnyChar> = name.clone();
                        {
                            let mut name = name.clone();
                            let mut test = test.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<DafnyChar>>{
            if int!(0) < crate::Std::Parsers::InputString::_default::Length(input) && (&test)(&crate::Std::Parsers::InputString::_default::CharAt(input, &int!(0))) {
                Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<DafnyChar> {
                        result: crate::Std::Parsers::InputString::_default::CharAt(input, &int!(0)),
                        remaining: crate::Std::Parsers::InputString::_default::Drop(input, &int!(1))
                    })
            } else {
                Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<DafnyChar> {
                        level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}),
                        data: Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                    message: string_of("expected a ").concat(&name),
                                    remaining: input.clone(),
                                    next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                })
                    })
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8757,3)
                pub fn DigitToInt(c: &DafnyChar) -> DafnyInt {
                    if c.clone() == DafnyChar(char::from_u32(48).unwrap()) {
                        int!(0)
                    } else {
                        if c.clone() == DafnyChar(char::from_u32(49).unwrap()) {
                            int!(1)
                        } else {
                            if c.clone() == DafnyChar(char::from_u32(50).unwrap()) {
                                int!(2)
                            } else {
                                if c.clone() == DafnyChar(char::from_u32(51).unwrap()) {
                                    int!(3)
                                } else {
                                    if c.clone() == DafnyChar(char::from_u32(52).unwrap()) {
                                        int!(4)
                                    } else {
                                        if c.clone() == DafnyChar(char::from_u32(53).unwrap()) {
                                            int!(5)
                                        } else {
                                            if c.clone() == DafnyChar(char::from_u32(54).unwrap()) {
                                                int!(6)
                                            } else {
                                                if c.clone() == DafnyChar(char::from_u32(55).unwrap()) {
                                                    int!(7)
                                                } else {
                                                    if c.clone() == DafnyChar(char::from_u32(56).unwrap()) {
                                                        int!(8)
                                                    } else {
                                                        if c.clone() == DafnyChar(char::from_u32(57).unwrap()) {
                                                            int!(9)
                                                        } else {
                                                            int!(-1)
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8784,3)
                pub fn StringToInt(s: &Sequence<DafnyChar>) -> DafnyInt {
                    if s.cardinality() == int!(0) {
                        int!(0)
                    } else {
                        if s.cardinality() == int!(1) {
                            crate::Std::Parsers::StringParsers::_default::DigitToInt(&s.get(&int!(0)))
                        } else {
                            if s.get(&int!(0)) == DafnyChar(char::from_u32(45).unwrap()) {
                                int!(0) - crate::Std::Parsers::StringParsers::_default::StringToInt(&s.drop(&int!(1)))
                            } else {
                                crate::Std::Parsers::StringParsers::_default::StringToInt(&s.slice(&int!(0), &(s.cardinality() - int!(1)))) * int!(10) + crate::Std::Parsers::StringParsers::_default::StringToInt(&s.slice(&(s.cardinality() - int!(1)), &s.cardinality()))
                            }
                        }
                    }
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9576,3)
            #[derive(Clone)]
            pub enum CodeLocation {
                CodeLocation {
                    lineNumber: nat,
                    colNumber: nat,
                    lineStr: Sequence<DafnyChar>
                }
            }

            impl CodeLocation {
                /// Returns a borrow of the field lineNumber
                pub fn lineNumber(&self) -> &nat {
                    match self {
                        CodeLocation::CodeLocation{lineNumber, colNumber, lineStr, } => lineNumber,
                    }
                }
                /// Returns a borrow of the field colNumber
                pub fn colNumber(&self) -> &nat {
                    match self {
                        CodeLocation::CodeLocation{lineNumber, colNumber, lineStr, } => colNumber,
                    }
                }
                /// Returns a borrow of the field lineStr
                pub fn lineStr(&self) -> &Sequence<DafnyChar> {
                    match self {
                        CodeLocation::CodeLocation{lineNumber, colNumber, lineStr, } => lineStr,
                    }
                }
            }

            impl Debug
                for CodeLocation {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for CodeLocation {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        CodeLocation::CodeLocation{lineNumber, colNumber, lineStr, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.CodeLocation.CodeLocation(")?;
                            DafnyPrint::fmt_print(lineNumber, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(colNumber, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(lineStr, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for CodeLocation {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (CodeLocation::CodeLocation{lineNumber, colNumber, lineStr, }, CodeLocation::CodeLocation{lineNumber: _2_lineNumber, colNumber: _2_colNumber, lineStr: _2_lineStr, }) => {
                            lineNumber == _2_lineNumber && colNumber == _2_colNumber && lineStr == _2_lineStr
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for CodeLocation {}

            impl Hash
                for CodeLocation {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        CodeLocation::CodeLocation{lineNumber, colNumber, lineStr, } => {
                            Hash::hash(lineNumber, _state);
                            Hash::hash(colNumber, _state);
                            Hash::hash(lineStr, _state)
                        },
                    }
                }
            }

            impl AsRef<CodeLocation>
                for CodeLocation {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9578,3)
            #[derive(Clone)]
            pub enum ExtractLineMutableState {
                ExtractLineMutableState {
                    input: Sequence<DafnyChar>,
                    pos: nat,
                    startLinePos: nat,
                    i: nat,
                    lineNumber: nat,
                    colNumber: nat
                }
            }

            impl ExtractLineMutableState {
                /// Returns a borrow of the field input
                pub fn input(&self) -> &Sequence<DafnyChar> {
                    match self {
                        ExtractLineMutableState::ExtractLineMutableState{input, pos, startLinePos, i, lineNumber, colNumber, } => input,
                    }
                }
                /// Returns a borrow of the field pos
                pub fn pos(&self) -> &nat {
                    match self {
                        ExtractLineMutableState::ExtractLineMutableState{input, pos, startLinePos, i, lineNumber, colNumber, } => pos,
                    }
                }
                /// Returns a borrow of the field startLinePos
                pub fn startLinePos(&self) -> &nat {
                    match self {
                        ExtractLineMutableState::ExtractLineMutableState{input, pos, startLinePos, i, lineNumber, colNumber, } => startLinePos,
                    }
                }
                /// Returns a borrow of the field i
                pub fn i(&self) -> &nat {
                    match self {
                        ExtractLineMutableState::ExtractLineMutableState{input, pos, startLinePos, i, lineNumber, colNumber, } => i,
                    }
                }
                /// Returns a borrow of the field lineNumber
                pub fn lineNumber(&self) -> &nat {
                    match self {
                        ExtractLineMutableState::ExtractLineMutableState{input, pos, startLinePos, i, lineNumber, colNumber, } => lineNumber,
                    }
                }
                /// Returns a borrow of the field colNumber
                pub fn colNumber(&self) -> &nat {
                    match self {
                        ExtractLineMutableState::ExtractLineMutableState{input, pos, startLinePos, i, lineNumber, colNumber, } => colNumber,
                    }
                }
            }

            impl Debug
                for ExtractLineMutableState {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for ExtractLineMutableState {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        ExtractLineMutableState::ExtractLineMutableState{input, pos, startLinePos, i, lineNumber, colNumber, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.ExtractLineMutableState.ExtractLineMutableState(")?;
                            DafnyPrint::fmt_print(input, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(pos, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(startLinePos, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(i, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(lineNumber, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(colNumber, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for ExtractLineMutableState {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (ExtractLineMutableState::ExtractLineMutableState{input, pos, startLinePos, i, lineNumber, colNumber, }, ExtractLineMutableState::ExtractLineMutableState{input: _2_input, pos: _2_pos, startLinePos: _2_startLinePos, i: _2_i, lineNumber: _2_lineNumber, colNumber: _2_colNumber, }) => {
                            input == _2_input && pos == _2_pos && startLinePos == _2_startLinePos && i == _2_i && lineNumber == _2_lineNumber && colNumber == _2_colNumber
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for ExtractLineMutableState {}

            impl Hash
                for ExtractLineMutableState {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        ExtractLineMutableState::ExtractLineMutableState{input, pos, startLinePos, i, lineNumber, colNumber, } => {
                            Hash::hash(input, _state);
                            Hash::hash(pos, _state);
                            Hash::hash(startLinePos, _state);
                            Hash::hash(i, _state);
                            Hash::hash(lineNumber, _state);
                            Hash::hash(colNumber, _state)
                        },
                    }
                }
            }

            impl AsRef<ExtractLineMutableState>
                for ExtractLineMutableState {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8822,3)
            #[derive(Clone)]
            pub enum FailureData {
                FailureData {
                    message: Sequence<DafnyChar>,
                    remaining: Input,
                    next: Rc<Option<Rc<crate::Std::Parsers::StringParsers::FailureData>>>
                }
            }

            impl FailureData {
                /// DafnyStandardLibraries-rs.dfy(8823,5)
                pub fn Concat(&self, other: &Rc<crate::Std::Parsers::StringParsers::FailureData>) -> Rc<crate::Std::Parsers::StringParsers::FailureData> {
                    if self.next().clone() == Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {}) {
                        let mut _dt__update__tmp_h0: Rc<crate::Std::Parsers::StringParsers::FailureData> = Rc::new(self.clone());
                        let mut _dt__update_hnext_h0: Rc<Option<Rc<crate::Std::Parsers::StringParsers::FailureData>>> = Rc::new(Option::Some::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {
                                    value: other.clone()
                                });
                        Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                message: _dt__update__tmp_h0.message().clone(),
                                remaining: _dt__update__tmp_h0.remaining().clone(),
                                next: _dt__update_hnext_h0.clone()
                            })
                    } else {
                        Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                message: self.message().clone(),
                                remaining: self.remaining().clone(),
                                next: Rc::new(Option::Some::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {
                                            value: self.next().value().Concat(other)
                                        })
                            })
                    }
                }
                /// Returns a borrow of the field message
                pub fn message(&self) -> &Sequence<DafnyChar> {
                    match self {
                        FailureData::FailureData{message, remaining, next, } => message,
                    }
                }
                /// Returns a borrow of the field remaining
                pub fn remaining(&self) -> &Input {
                    match self {
                        FailureData::FailureData{message, remaining, next, } => remaining,
                    }
                }
                /// Returns a borrow of the field next
                pub fn next(&self) -> &Rc<Option<Rc<crate::Std::Parsers::StringParsers::FailureData>>> {
                    match self {
                        FailureData::FailureData{message, remaining, next, } => next,
                    }
                }
            }

            impl Debug
                for FailureData {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for FailureData {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        FailureData::FailureData{message, remaining, next, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.FailureData.FailureData(")?;
                            DafnyPrint::fmt_print(message, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(remaining, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(next, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for FailureData {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (FailureData::FailureData{message, remaining, next, }, FailureData::FailureData{message: _2_message, remaining: _2_remaining, next: _2_next, }) => {
                            message == _2_message && remaining == _2_remaining && next == _2_next
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for FailureData {}

            impl Hash
                for FailureData {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        FailureData::FailureData{message, remaining, next, } => {
                            Hash::hash(message, _state);
                            Hash::hash(remaining, _state);
                            Hash::hash(next, _state)
                        },
                    }
                }
            }

            impl AsRef<FailureData>
                for FailureData {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8832,3)
            #[derive(Clone)]
            pub enum FailureLevel {
                Fatal {},
                Recoverable {}
            }

            impl FailureLevel {}

            impl Debug
                for FailureLevel {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for FailureLevel {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        FailureLevel::Fatal{} => {
                            write!(_formatter, "Std.Parsers.StringParsers.FailureLevel.Fatal")?;
                            Ok(())
                        },
                        FailureLevel::Recoverable{} => {
                            write!(_formatter, "Std.Parsers.StringParsers.FailureLevel.Recoverable")?;
                            Ok(())
                        },
                    }
                }
            }

            impl FailureLevel {
                /// Enumerates all possible values of FailureLevel
                pub fn _AllSingletonConstructors() -> SequenceIter<Rc<FailureLevel>> {
                    seq![Rc::new(FailureLevel::Fatal {}), Rc::new(FailureLevel::Recoverable {})].iter()
                }
            }

            impl PartialEq
                for FailureLevel {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (FailureLevel::Fatal{}, FailureLevel::Fatal{}) => {
                            true
                        },
                        (FailureLevel::Recoverable{}, FailureLevel::Recoverable{}) => {
                            true
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for FailureLevel {}

            impl Hash
                for FailureLevel {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        FailureLevel::Fatal{} => {
                            
                        },
                        FailureLevel::Recoverable{} => {
                            
                        },
                    }
                }
            }

            impl AsRef<FailureLevel>
                for FailureLevel {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8834,3)
            #[derive(Clone)]
            pub enum ParseResult<R: DafnyType> {
                ParseFailure {
                    level: Rc<crate::Std::Parsers::StringParsers::FailureLevel>,
                    data: Rc<crate::Std::Parsers::StringParsers::FailureData>
                },
                ParseSuccess {
                    result: R,
                    remaining: Input
                }
            }

            impl<R: DafnyType> ParseResult<R> {
                /// DafnyStandardLibraries-rs.dfy(8835,5)
                pub fn Remaining(&self) -> Input {
                    if matches!((&Rc::new(self.clone())).as_ref(), ParseSuccess{ .. }) {
                        self.remaining().clone()
                    } else {
                        self.data().remaining().clone()
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8843,5)
                pub fn IsFailure(&self) -> bool {
                    matches!((&Rc::new(self.clone())).as_ref(), ParseFailure{ .. })
                }
                /// DafnyStandardLibraries-rs.dfy(8848,5)
                pub fn IsFatalFailure(&self) -> bool {
                    matches!((&Rc::new(self.clone())).as_ref(), ParseFailure{ .. }) && self.level().clone() == Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {})
                }
                /// DafnyStandardLibraries-rs.dfy(8854,5)
                pub fn IsFatal(&self) -> bool {
                    self.level().clone() == Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {})
                }
                /// DafnyStandardLibraries-rs.dfy(8860,5)
                pub fn PropagateFailure<_U: DafnyType>(&self) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_U>> {
                    Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_U> {
                            level: self.level().clone(),
                            data: self.data().clone()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8866,5)
                pub fn Extract(&self) -> (R, Input) {
                    (
                        self.result().clone(),
                        self.remaining().clone()
                    )
                }
                /// DafnyStandardLibraries-rs.dfy(8872,5)
                pub fn Map<___R_k: DafnyType>(&self, f: &Rc<dyn ::std::ops::Fn(&R) -> ___R_k>) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<___R_k>> {
                    let mut _source0: Rc<crate::Std::Parsers::StringParsers::ParseResult<R>> = Rc::new(self.clone());
                    if matches!((&_source0).as_ref(), ParseFailure{ .. }) {
                        let mut ___mcc_h0: Rc<crate::Std::Parsers::StringParsers::FailureLevel> = _source0.level().clone();
                        let mut ___mcc_h1: Rc<crate::Std::Parsers::StringParsers::FailureData> = _source0.data().clone();
                        let mut data: Rc<crate::Std::Parsers::StringParsers::FailureData> = ___mcc_h1.clone();
                        let mut level: Rc<crate::Std::Parsers::StringParsers::FailureLevel> = ___mcc_h0.clone();
                        Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<___R_k> {
                                level: level.clone(),
                                data: data.clone()
                            })
                    } else {
                        let mut ___mcc_h2: R = _source0.result().clone();
                        let mut ___mcc_h3: Input = _source0.remaining().clone();
                        let mut remaining: Input = ___mcc_h3.clone();
                        let mut result: R = ___mcc_h2.clone();
                        Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseSuccess::<___R_k> {
                                result: f(&result),
                                remaining: remaining.clone()
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8881,5)
                pub fn MapRecoverableError(&self, f: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringParsers::FailureData>) -> Rc<crate::Std::Parsers::StringParsers::FailureData>>) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<R>> {
                    let mut _source0: Rc<crate::Std::Parsers::StringParsers::ParseResult<R>> = Rc::new(self.clone());
                    if matches!((&_source0).as_ref(), ParseFailure{ .. }) {
                        let mut ___mcc_h0: Rc<crate::Std::Parsers::StringParsers::FailureLevel> = _source0.level().clone();
                        let mut ___mcc_h1: Rc<crate::Std::Parsers::StringParsers::FailureData> = _source0.data().clone();
                        let mut _source1: Rc<crate::Std::Parsers::StringParsers::FailureLevel> = ___mcc_h0.clone();
                        if matches!((&_source1).as_ref(), Fatal{ .. }) {
                            Rc::new(self.clone())
                        } else {
                            let mut data: Rc<crate::Std::Parsers::StringParsers::FailureData> = ___mcc_h1.clone();
                            Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<R> {
                                    level: Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}),
                                    data: f(&data)
                                })
                        }
                    } else {
                        let mut ___mcc_h4: R = _source0.result().clone();
                        let mut ___mcc_h5: Input = _source0.remaining().clone();
                        Rc::new(self.clone())
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8890,5)
                pub fn NeedsAlternative(&self, input: &Input) -> bool {
                    matches!((&Rc::new(self.clone())).as_ref(), ParseFailure{ .. }) && self.level().clone() == Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Recoverable {}) && input.clone() == self.Remaining()
                }
                /// Gets the field level for all enum members which have it
                pub fn level(&self) -> &Rc<crate::Std::Parsers::StringParsers::FailureLevel> {
                    match self {
                        ParseResult::ParseFailure{level, data, } => level,
                        ParseResult::ParseSuccess{result, remaining, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field data for all enum members which have it
                pub fn data(&self) -> &Rc<crate::Std::Parsers::StringParsers::FailureData> {
                    match self {
                        ParseResult::ParseFailure{level, data, } => data,
                        ParseResult::ParseSuccess{result, remaining, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field result for all enum members which have it
                pub fn result(&self) -> &R {
                    match self {
                        ParseResult::ParseFailure{level, data, } => panic!("field does not exist on this variant"),
                        ParseResult::ParseSuccess{result, remaining, } => result,
                    }
                }
                /// Gets the field remaining for all enum members which have it
                pub fn remaining(&self) -> &Input {
                    match self {
                        ParseResult::ParseFailure{level, data, } => panic!("field does not exist on this variant"),
                        ParseResult::ParseSuccess{result, remaining, } => remaining,
                    }
                }
            }

            impl<R: DafnyType> Debug
                for ParseResult<R> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<R: DafnyType> DafnyPrint
                for ParseResult<R> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        ParseResult::ParseFailure{level, data, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.ParseResult.ParseFailure(")?;
                            DafnyPrint::fmt_print(level, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(data, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        ParseResult::ParseSuccess{result, remaining, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.ParseResult.ParseSuccess(")?;
                            DafnyPrint::fmt_print(result, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(remaining, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<R: DafnyType> ParseResult<R> {
                /// Given type parameter conversions, returns a lambda to convert this structure
                pub fn coerce<__T0: DafnyType>(f_0: Rc<impl ::std::ops::Fn(R) -> __T0 + 'static>) -> Rc<impl ::std::ops::Fn(ParseResult<R>) -> ParseResult<__T0>> {
                    Rc::new(move |this: Self| -> ParseResult<__T0>{
                            match this {
                                ParseResult::ParseFailure{level, data, } => {
                                    ParseResult::ParseFailure {
                                        level: upcast_id::<Rc<crate::Std::Parsers::StringParsers::FailureLevel>>()(level),
                                        data: upcast_id::<Rc<crate::Std::Parsers::StringParsers::FailureData>>()(data)
                                    }
                                },
                                ParseResult::ParseSuccess{result, remaining, } => {
                                    ParseResult::ParseSuccess {
                                        result: f_0.clone()(result),
                                        remaining: upcast_id::<Input>()(remaining)
                                    }
                                },
                            }
                        })
                }
            }

            impl<R: DafnyType + Eq + Hash> PartialEq
                for ParseResult<R> {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (ParseResult::ParseFailure{level, data, }, ParseResult::ParseFailure{level: _2_level, data: _2_data, }) => {
                            level == _2_level && data == _2_data
                        },
                        (ParseResult::ParseSuccess{result, remaining, }, ParseResult::ParseSuccess{result: _2_result, remaining: _2_remaining, }) => {
                            result == _2_result && remaining == _2_remaining
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl<R: DafnyType + Eq + Hash> Eq
                for ParseResult<R> {}

            impl<R: DafnyType + Hash> Hash
                for ParseResult<R> {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        ParseResult::ParseFailure{level, data, } => {
                            Hash::hash(level, _state);
                            Hash::hash(data, _state)
                        },
                        ParseResult::ParseSuccess{result, remaining, } => {
                            Hash::hash(result, _state);
                            Hash::hash(remaining, _state)
                        },
                    }
                }
            }

            impl<R: DafnyType> AsRef<ParseResult<R>>
                for ParseResult<R> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8898,3)
            #[derive(Clone)]
            pub enum SeqB<A: DafnyType> {
                SeqBCons {
                    last: A,
                    init: Rc<crate::Std::Parsers::StringParsers::SeqB<A>>
                },
                SeqBNil {}
            }

            impl<A: DafnyType> SeqB<A> {
                /// DafnyStandardLibraries-rs.dfy(8899,5)
                pub fn Append(&self, elem: &A) -> Rc<crate::Std::Parsers::StringParsers::SeqB<A>> {
                    Rc::new(crate::Std::Parsers::StringParsers::SeqB::SeqBCons::<A> {
                            last: elem.clone(),
                            init: Rc::new(self.clone())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8904,5)
                pub fn Length(&self) -> nat {
                    let mut _accumulator: nat = int!(0);
                    let mut _this = Rc::new(self.clone());
                    'TAIL_CALL_START: loop {
                        if matches!((&_this).as_ref(), SeqBNil{ .. }) {
                            return int!(0) + _accumulator.clone();
                        } else {
                            _accumulator = _accumulator.clone() + int!(1);
                            let mut _in0: Rc<crate::Std::Parsers::StringParsers::SeqB<A>> = _this.init().clone();
                            _this = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8912,5)
                pub fn ToSequence(&self) -> Sequence<A> {
                    let mut _hresult = MaybePlacebo::<Sequence<A>>::new();
                    if matches!((&Rc::new(self.clone())).as_ref(), SeqBNil{ .. }) {
                        _hresult = MaybePlacebo::from(seq![] as Sequence<A>);
                        return _hresult.read();
                    };
                    let mut defaultElem: A = self.last().clone();
                    let mut l: nat = self.Length();
                    let mut elements = MaybePlacebo::<Object<[A]>>::new();
                    let mut _init0: Rc<dyn ::std::ops::Fn(&nat) -> A> = {
                            let defaultElem: A = defaultElem.clone();
                            {
                                let mut defaultElem = defaultElem.clone();
                                Rc::new(move |i: &nat| -> A{
            defaultElem.clone()
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        };
                    let mut _nw0: Object<[MaybeUninit<A>]> = array::placebos_usize_object::<A>(DafnyUsize::into_usize(l.clone()));
                    for __i0_0 in integer_range(truncate!(int!(0), usize), rd!(_nw0.clone()).len()) {
                        {
                            let __idx0 = DafnyUsize::into_usize(__i0_0.clone());
                            ::dafny_runtime::md!(_nw0)[__idx0] = MaybeUninit::new((&_init0)(&int!(__i0_0.clone())));
                        }
                    }
                    elements = MaybePlacebo::from(array::construct_object(_nw0.clone()));
                    let mut t: Rc<crate::Std::Parsers::StringParsers::SeqB<A>> = Rc::new(self.clone());
                    let mut i: DafnyInt = l.clone();
                    while !matches!((&t).as_ref(), SeqBNil{ .. }) {
                        i = i.clone() - int!(1);
                        {
                            let __idx0 = DafnyUsize::into_usize(i.clone());
                            ::dafny_runtime::md!(elements.read())[__idx0] = t.last().clone();
                        };
                        t = t.init().clone();
                    };
                    _hresult = MaybePlacebo::from(Sequence::from_array_object(&elements.read()));
                    return _hresult.read();
                }
                /// Gets the field last for all enum members which have it
                pub fn last(&self) -> &A {
                    match self {
                        SeqB::SeqBCons{last, init, } => last,
                        SeqB::SeqBNil{} => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field init for all enum members which have it
                pub fn init(&self) -> &Rc<crate::Std::Parsers::StringParsers::SeqB<A>> {
                    match self {
                        SeqB::SeqBCons{last, init, } => init,
                        SeqB::SeqBNil{} => panic!("field does not exist on this variant"),
                    }
                }
            }

            impl<A: DafnyType> Debug
                for SeqB<A> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<A: DafnyType> DafnyPrint
                for SeqB<A> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        SeqB::SeqBCons{last, init, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.SeqB.SeqBCons(")?;
                            DafnyPrint::fmt_print(last, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(init, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        SeqB::SeqBNil{} => {
                            write!(_formatter, "Std.Parsers.StringParsers.SeqB.SeqBNil")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<A: DafnyType + Eq + Hash> PartialEq
                for SeqB<A> {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (SeqB::SeqBCons{last, init, }, SeqB::SeqBCons{last: _2_last, init: _2_init, }) => {
                            last == _2_last && init == _2_init
                        },
                        (SeqB::SeqBNil{}, SeqB::SeqBNil{}) => {
                            true
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl<A: DafnyType + Eq + Hash> Eq
                for SeqB<A> {}

            impl<A: DafnyType + Hash> Hash
                for SeqB<A> {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        SeqB::SeqBCons{last, init, } => {
                            Hash::hash(last, _state);
                            Hash::hash(init, _state)
                        },
                        SeqB::SeqBNil{} => {
                            
                        },
                    }
                }
            }

            impl<A: DafnyType> AsRef<SeqB<A>>
                for SeqB<A> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8944,3)
            #[derive(Clone)]
            pub enum RecursiveNoStackResult<R: DafnyType> {
                RecursiveReturn {
                    _h4: R
                },
                RecursiveContinue {
                    _h5: Rc<dyn ::std::ops::Fn(&R) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<R>>>>>>
                }
            }

            impl<R: DafnyType> RecursiveNoStackResult<R> {
                /// Gets the field _h4 for all enum members which have it
                pub fn _h4(&self) -> &R {
                    match self {
                        RecursiveNoStackResult::RecursiveReturn{_h4, } => _h4,
                        RecursiveNoStackResult::RecursiveContinue{_h5, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field _h5 for all enum members which have it
                pub fn _h5(&self) -> &Rc<dyn ::std::ops::Fn(&R) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<R>>>>>> {
                    match self {
                        RecursiveNoStackResult::RecursiveReturn{_h4, } => panic!("field does not exist on this variant"),
                        RecursiveNoStackResult::RecursiveContinue{_h5, } => _h5,
                    }
                }
            }

            impl<R: DafnyType> Debug
                for RecursiveNoStackResult<R> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<R: DafnyType> DafnyPrint
                for RecursiveNoStackResult<R> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        RecursiveNoStackResult::RecursiveReturn{_h4, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.RecursiveNoStackResult.RecursiveReturn(")?;
                            DafnyPrint::fmt_print(_h4, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        RecursiveNoStackResult::RecursiveContinue{_h5, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.RecursiveNoStackResult.RecursiveContinue(")?;
                            write!(_formatter, "<function>")?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<R: DafnyType> AsRef<RecursiveNoStackResult<R>>
                for RecursiveNoStackResult<R> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8948,3)
            #[derive(Clone)]
            pub enum RecursiveDef<R: DafnyType> {
                RecursiveDef {
                    order: nat,
                    definition: Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<R>>>>
                }
            }

            impl<R: DafnyType> RecursiveDef<R> {
                /// Returns a borrow of the field order
                pub fn order(&self) -> &nat {
                    match self {
                        RecursiveDef::RecursiveDef{order, definition, } => order,
                    }
                }
                /// Returns a borrow of the field definition
                pub fn definition(&self) -> &Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<R>>>> {
                    match self {
                        RecursiveDef::RecursiveDef{order, definition, } => definition,
                    }
                }
            }

            impl<R: DafnyType> Debug
                for RecursiveDef<R> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<R: DafnyType> DafnyPrint
                for RecursiveDef<R> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        RecursiveDef::RecursiveDef{order, definition, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.RecursiveDef.RecursiveDef(")?;
                            DafnyPrint::fmt_print(order, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            write!(_formatter, "<function>")?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<R: DafnyType> AsRef<RecursiveDef<R>>
                for RecursiveDef<R> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }
        }
    }

    /// DafnyStandardLibraries-rs.dfy(9581,1)
    pub mod Relations {
        
    }

    /// DafnyStandardLibraries-rs.dfy(9717,1)
    pub mod Strings {
        pub use ::dafny_runtime::_System::nat;
        pub use ::dafny_runtime::Sequence;
        pub use ::dafny_runtime::DafnyChar;
        pub use ::dafny_runtime::DafnyInt;
        pub use ::std::primitive::char;
        pub use ::dafny_runtime::set;
        pub use ::std::rc::Rc;
        pub use crate::Std::Wrappers::Option;
        pub use ::dafny_runtime::string_of;
        pub use ::dafny_runtime::seq;

        pub struct _default {}

        impl _default {
            /// DafnyStandardLibraries-rs.dfy(9719,3)
            pub fn OfNat(n: &nat) -> Sequence<DafnyChar> {
                crate::Std::Strings::DecimalConversion::_default::OfNat(n)
            }
            /// DafnyStandardLibraries-rs.dfy(9726,3)
            pub fn OfInt(n: &DafnyInt) -> Sequence<DafnyChar> {
                crate::Std::Strings::DecimalConversion::_default::OfInt(n, &DafnyChar(char::from_u32(45).unwrap()))
            }
            /// DafnyStandardLibraries-rs.dfy(9732,3)
            pub fn ToNat(str: &Sequence<DafnyChar>) -> nat {
                crate::Std::Strings::DecimalConversion::_default::ToNat(str)
            }
            /// DafnyStandardLibraries-rs.dfy(9740,3)
            pub fn ToInt(str: &Sequence<DafnyChar>) -> DafnyInt {
                crate::Std::Strings::DecimalConversion::_default::ToInt(str, &DafnyChar(char::from_u32(45).unwrap()))
            }
            /// DafnyStandardLibraries-rs.dfy(9747,3)
            pub fn EscapeQuotes(str: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                crate::Std::Strings::CharStrEscaping::_default::Escape(str, &set!{DafnyChar(char::from_u32(34).unwrap()), DafnyChar(char::from_u32(39).unwrap())}, &DafnyChar(char::from_u32(92).unwrap()))
            }
            /// DafnyStandardLibraries-rs.dfy(9752,3)
            pub fn UnescapeQuotes(str: &Sequence<DafnyChar>) -> Rc<Option<Sequence<DafnyChar>>> {
                crate::Std::Strings::CharStrEscaping::_default::Unescape(str, &DafnyChar(char::from_u32(92).unwrap()))
            }
            /// DafnyStandardLibraries-rs.dfy(9757,3)
            pub fn OfBool(b: bool) -> Sequence<DafnyChar> {
                if b {
                    string_of("true")
                } else {
                    string_of("false")
                }
            }
            /// DafnyStandardLibraries-rs.dfy(9765,3)
            pub fn OfChar(c: &DafnyChar) -> Sequence<DafnyChar> {
                seq![c.clone()]
            }
        }

        /// DafnyStandardLibraries-rs.dfy(9964,3)
        pub mod CharStrEscaping {
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::dafny_runtime::Set;
            pub use ::dafny_runtime::seq;
            pub use ::dafny_runtime::int;
            pub use ::std::rc::Rc;
            pub use crate::Std::Wrappers::Option;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(9897,5)
                pub fn Escape(str: &Sequence<DafnyChar>, mustEscape: &Set<DafnyChar>, escape: &DafnyChar) -> Sequence<DafnyChar> {
                    let mut _accumulator: Sequence<DafnyChar> = seq![] as Sequence<DafnyChar>;
                    let mut _r0 = str.clone();
                    let mut _r1 = mustEscape.clone();
                    let mut _r2 = escape.clone();
                    'TAIL_CALL_START: loop {
                        let str = _r0;
                        let mustEscape = _r1;
                        let escape = _r2;
                        if str.clone().to_array().len() == 0 {
                            return _accumulator.concat(&str);
                        } else {
                            if mustEscape.contains(&str.get(&int!(0))) {
                                _accumulator = _accumulator.concat(&seq![escape.clone(), str.get(&int!(0))]);
                                let mut _in0: Sequence<DafnyChar> = str.drop(&int!(1));
                                let mut _in1: Set<DafnyChar> = mustEscape.clone();
                                let mut _in2: DafnyChar = escape.clone();
                                _r0 = _in0.clone();
                                _r1 = _in1.clone();
                                _r2 = _in2.clone();
                                continue 'TAIL_CALL_START;
                            } else {
                                _accumulator = _accumulator.concat(&seq![str.get(&int!(0))]);
                                let mut _in3: Sequence<DafnyChar> = str.drop(&int!(1));
                                let mut _in4: Set<DafnyChar> = mustEscape.clone();
                                let mut _in5: DafnyChar = escape.clone();
                                _r0 = _in3.clone();
                                _r1 = _in4.clone();
                                _r2 = _in5.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9907,5)
                pub fn Unescape(str: &Sequence<DafnyChar>, escape: &DafnyChar) -> Rc<Option<Sequence<DafnyChar>>> {
                    if str.clone().to_array().len() == 0 {
                        Rc::new(Option::Some::<Sequence<DafnyChar>> {
                                value: str.clone()
                            })
                    } else {
                        if str.get(&int!(0)) == escape.clone() {
                            if int!(1) < str.cardinality() {
                                let mut valueOrError0: Rc<Option<Sequence<DafnyChar>>> = crate::Std::Strings::CharStrEscaping::_default::Unescape(&str.drop(&int!(2)), escape);
                                if valueOrError0.IsFailure() {
                                    valueOrError0.PropagateFailure::<Sequence<DafnyChar>>()
                                } else {
                                    let mut tl: Sequence<DafnyChar> = valueOrError0.Extract();
                                    Rc::new(Option::Some::<Sequence<DafnyChar>> {
                                            value: seq![str.get(&int!(1))].concat(&tl)
                                        })
                                }
                            } else {
                                Rc::new(Option::None::<Sequence<DafnyChar>> {})
                            }
                        } else {
                            let mut valueOrError1: Rc<Option<Sequence<DafnyChar>>> = crate::Std::Strings::CharStrEscaping::_default::Unescape(&str.drop(&int!(1)), escape);
                            if valueOrError1.IsFailure() {
                                valueOrError1.PropagateFailure::<Sequence<DafnyChar>>()
                            } else {
                                let mut tl: Sequence<DafnyChar> = valueOrError1.Extract();
                                Rc::new(Option::Some::<Sequence<DafnyChar>> {
                                        value: seq![str.get(&int!(0))].concat(&tl)
                                    })
                            }
                        }
                    }
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(9950,3)
        pub mod DecimalConversion {
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::seq;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::itertools::Itertools;
            pub use ::std::rc::Rc;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::euclidian_modulo;
            pub use ::dafny_runtime::euclidian_division;
            pub use ::dafny_runtime::string_of;
            pub use ::dafny_runtime::Map;
            pub use ::dafny_runtime::map;
            pub use ::std::primitive::char;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(9787,5)
                pub fn BASE() -> nat {
                    crate::Std::Strings::DecimalConversion::_default::base()
                }
                /// DafnyStandardLibraries-rs.dfy(9792,5)
                pub fn IsDigitChar(c: &DafnyChar) -> bool {
                    crate::Std::Strings::DecimalConversion::_default::charToDigit().contains(c)
                }
                /// DafnyStandardLibraries-rs.dfy(9797,5)
                pub fn OfDigits(digits: &Sequence<crate::Std::Strings::DecimalConversion::digit>) -> Sequence<DafnyChar> {
                    let mut _accumulator: Sequence<DafnyChar> = seq![] as Sequence<DafnyChar>;
                    let mut _r0 = digits.clone();
                    'TAIL_CALL_START: loop {
                        let digits = _r0;
                        if digits.clone().to_array().len() == 0 {
                            return (seq![] as Sequence<DafnyChar>).concat(&_accumulator);
                        } else {
                            _accumulator = seq![crate::Std::Strings::DecimalConversion::_default::chars().get(&digits.get(&int!(0)))].concat(&_accumulator);
                            let mut _in0: Sequence<crate::Std::Strings::DecimalConversion::digit> = digits.drop(&int!(1));
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9807,5)
                pub fn OfNat(n: &nat) -> Sequence<DafnyChar> {
                    if n.clone() == int!(0) {
                        seq![crate::Std::Strings::DecimalConversion::_default::chars().get(&int!(0))]
                    } else {
                        crate::Std::Strings::DecimalConversion::_default::OfDigits(&crate::Std::Strings::DecimalConversion::_default::FromNat(n))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9817,5)
                pub fn IsNumberStr(str: &Sequence<DafnyChar>, minus: &DafnyChar) -> bool {
                    !(!(str.clone().to_array().len() == 0)) || (str.get(&int!(0)) == minus.clone() || crate::Std::Strings::DecimalConversion::_default::charToDigit().contains(&str.get(&int!(0)))) && Itertools::unique((&str.drop(&int!(1))).iter()).all(({
                            let mut str = str.clone();
                            Rc::new(move |__forall_var_0: DafnyChar| -> bool{
            let mut c: DafnyChar = __forall_var_0.clone();
            !str.drop(&int!(1)).contains(&c) || crate::Std::Strings::DecimalConversion::_default::IsDigitChar(&c)
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                        }).as_ref())
                }
                /// DafnyStandardLibraries-rs.dfy(9825,5)
                pub fn OfInt(n: &DafnyInt, minus: &DafnyChar) -> Sequence<DafnyChar> {
                    if !(n.clone() < int!(0)) {
                        crate::Std::Strings::DecimalConversion::_default::OfNat(n)
                    } else {
                        seq![minus.clone()].concat(&crate::Std::Strings::DecimalConversion::_default::OfNat(&(int!(0) - n.clone())))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9835,5)
                pub fn ToNat(str: &Sequence<DafnyChar>) -> nat {
                    if str.clone().to_array().len() == 0 {
                        int!(0)
                    } else {
                        let mut c: DafnyChar = str.get(&(str.cardinality() - int!(1)));
                        crate::Std::Strings::DecimalConversion::_default::ToNat(&str.take(&(str.cardinality() - int!(1)))) * crate::Std::Strings::DecimalConversion::_default::base() + crate::Std::Strings::DecimalConversion::_default::charToDigit().get(&c)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9875,5)
                pub fn ToInt(str: &Sequence<DafnyChar>, minus: &DafnyChar) -> DafnyInt {
                    if seq![minus.clone()] <= str.clone() {
                        int!(0) - crate::Std::Strings::DecimalConversion::_default::ToNat(&str.drop(&int!(1)))
                    } else {
                        crate::Std::Strings::DecimalConversion::_default::ToNat(str)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(2728,3)
                pub fn ToNatRight(xs: &Sequence<crate::Std::Strings::DecimalConversion::digit>) -> nat {
                    if xs.cardinality() == int!(0) {
                        int!(0)
                    } else {
                        crate::Std::Strings::DecimalConversion::_default::ToNatRight(&crate::Std::Collections::Seq::_default::DropFirst::<crate::Std::Strings::DecimalConversion::digit>(xs)) * crate::Std::Strings::DecimalConversion::_default::BASE() + crate::Std::Collections::Seq::_default::First::<crate::Std::Strings::DecimalConversion::digit>(xs)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(2736,3)
                pub fn ToNatLeft(xs: &Sequence<crate::Std::Strings::DecimalConversion::digit>) -> nat {
                    let mut _accumulator: nat = int!(0);
                    let mut _r0 = xs.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        if xs.cardinality() == int!(0) {
                            return int!(0) + _accumulator.clone();
                        } else {
                            _accumulator = crate::Std::Collections::Seq::_default::Last::<DafnyInt>(&xs) * crate::Std::Arithmetic::Power::_default::Pow(&crate::Std::Strings::DecimalConversion::_default::BASE(), &(xs.cardinality() - int!(1))) + _accumulator.clone();
                            let mut _in0: Sequence<crate::Std::Strings::DecimalConversion::digit> = crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::DecimalConversion::digit>(&xs);
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3020,3)
                pub fn FromNat(n: &nat) -> Sequence<crate::Std::Strings::DecimalConversion::digit> {
                    let mut _accumulator: Sequence<crate::Std::Strings::DecimalConversion::digit> = seq![] as Sequence<crate::Std::Strings::DecimalConversion::digit>;
                    let mut _r0 = n.clone();
                    'TAIL_CALL_START: loop {
                        let n = _r0;
                        if n.clone() == int!(0) {
                            return _accumulator.concat(&(seq![] as Sequence<DafnyInt>));
                        } else {
                            _accumulator = _accumulator.concat(&seq![euclidian_modulo(n.clone(), crate::Std::Strings::DecimalConversion::_default::BASE())]);
                            let mut _in0: DafnyInt = euclidian_division(n.clone(), crate::Std::Strings::DecimalConversion::_default::BASE());
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3104,3)
                pub fn SeqExtend(xs: &Sequence<crate::Std::Strings::DecimalConversion::digit>, n: &nat) -> Sequence<crate::Std::Strings::DecimalConversion::digit> {
                    let mut _r0 = xs.clone();
                    let mut _r1 = n.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        let n = _r1;
                        if !(xs.cardinality() < n.clone()) {
                            return xs.clone();
                        } else {
                            let mut _in0: Sequence<crate::Std::Strings::DecimalConversion::digit> = xs.concat(&seq![int!(0)]);
                            let mut _in1: nat = n.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3116,3)
                pub fn SeqExtendMultiple(xs: &Sequence<crate::Std::Strings::DecimalConversion::digit>, n: &nat) -> Sequence<crate::Std::Strings::DecimalConversion::digit> {
                    let mut newLen: DafnyInt = xs.cardinality() + n.clone() - euclidian_modulo(xs.cardinality(), n.clone());
                    crate::Std::Strings::DecimalConversion::_default::SeqExtend(xs, &newLen)
                }
                /// DafnyStandardLibraries-rs.dfy(3130,3)
                pub fn FromNatWithLen(n: &nat, len: &nat) -> Sequence<crate::Std::Strings::DecimalConversion::digit> {
                    crate::Std::Strings::DecimalConversion::_default::SeqExtend(&crate::Std::Strings::DecimalConversion::_default::FromNat(n), len)
                }
                /// DafnyStandardLibraries-rs.dfy(3153,3)
                pub fn SeqZero(len: &nat) -> Sequence<crate::Std::Strings::DecimalConversion::digit> {
                    let mut xs: Sequence<crate::Std::Strings::DecimalConversion::digit> = crate::Std::Strings::DecimalConversion::_default::FromNatWithLen(&int!(0), len);
                    xs.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(3182,3)
                pub fn SeqAdd(xs: &Sequence<crate::Std::Strings::DecimalConversion::digit>, ys: &Sequence<crate::Std::Strings::DecimalConversion::digit>) -> (Sequence<crate::Std::Strings::DecimalConversion::digit>, nat) {
                    if xs.cardinality() == int!(0) {
                        (
                            seq![] as Sequence<DafnyInt>,
                            int!(0)
                        )
                    } else {
                        let mut __let_tmp_rhs0: (Sequence<crate::Std::Strings::DecimalConversion::digit>, nat) = crate::Std::Strings::DecimalConversion::_default::SeqAdd(&crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::DecimalConversion::digit>(xs), &crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::DecimalConversion::digit>(ys));
                        let mut _zs_k: Sequence<crate::Std::Strings::DecimalConversion::digit> = __let_tmp_rhs0.0.clone();
                        let mut cin: nat = __let_tmp_rhs0.1.clone();
                        let mut sum: DafnyInt = crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) + crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) + cin.clone();
                        let mut __let_tmp_rhs1: (DafnyInt, DafnyInt) = if sum.clone() < crate::Std::Strings::DecimalConversion::_default::BASE() {
                                (
                                    sum.clone(),
                                    int!(0)
                                )
                            } else {
                                (
                                    sum.clone() - crate::Std::Strings::DecimalConversion::_default::BASE(),
                                    int!(1)
                                )
                            };
                        let mut sum_out: DafnyInt = __let_tmp_rhs1.0.clone();
                        let mut cout: DafnyInt = __let_tmp_rhs1.1.clone();
                        (
                            _zs_k.concat(&seq![sum_out.clone()]),
                            cout.clone()
                        )
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3229,3)
                pub fn SeqSub(xs: &Sequence<crate::Std::Strings::DecimalConversion::digit>, ys: &Sequence<crate::Std::Strings::DecimalConversion::digit>) -> (Sequence<crate::Std::Strings::DecimalConversion::digit>, nat) {
                    if xs.cardinality() == int!(0) {
                        (
                            seq![] as Sequence<DafnyInt>,
                            int!(0)
                        )
                    } else {
                        let mut __let_tmp_rhs0: (Sequence<crate::Std::Strings::DecimalConversion::digit>, nat) = crate::Std::Strings::DecimalConversion::_default::SeqSub(&crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::DecimalConversion::digit>(xs), &crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::DecimalConversion::digit>(ys));
                        let mut zs: Sequence<crate::Std::Strings::DecimalConversion::digit> = __let_tmp_rhs0.0.clone();
                        let mut cin: nat = __let_tmp_rhs0.1.clone();
                        let mut __let_tmp_rhs1: (DafnyInt, DafnyInt) = if !(crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) < crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) + cin.clone()) {
                                (
                                    crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) - crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) - cin.clone(),
                                    int!(0)
                                )
                            } else {
                                (
                                    crate::Std::Strings::DecimalConversion::_default::BASE() + crate::Std::Collections::Seq::_default::Last::<crate::Std::Strings::DecimalConversion::digit>(xs) - crate::Std::Collections::Seq::_default::Last::<crate::Std::Strings::DecimalConversion::digit>(ys) - cin.clone(),
                                    int!(1)
                                )
                            };
                        let mut diff_out: DafnyInt = __let_tmp_rhs1.0.clone();
                        let mut cout: DafnyInt = __let_tmp_rhs1.1.clone();
                        (
                            zs.concat(&seq![diff_out.clone()]),
                            cout.clone()
                        )
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9952,5)
                pub fn DIGITS() -> Sequence<DafnyChar> {
                    string_of("0123456789")
                }
                /// DafnyStandardLibraries-rs.dfy(9953,5)
                pub fn chars() -> Sequence<DafnyChar> {
                    crate::Std::Strings::DecimalConversion::_default::DIGITS()
                }
                /// DafnyStandardLibraries-rs.dfy(9781,5)
                pub fn base() -> DafnyInt {
                    crate::Std::Strings::DecimalConversion::_default::chars().cardinality()
                }
                /// DafnyStandardLibraries-rs.dfy(9954,5)
                pub fn charToDigit() -> Map<DafnyChar, crate::Std::Strings::DecimalConversion::digit> {
                    map![DafnyChar(char::from_u32(48).unwrap()) => int!(0), DafnyChar(char::from_u32(49).unwrap()) => int!(1), DafnyChar(char::from_u32(50).unwrap()) => int!(2), DafnyChar(char::from_u32(51).unwrap()) => int!(3), DafnyChar(char::from_u32(52).unwrap()) => int!(4), DafnyChar(char::from_u32(53).unwrap()) => int!(5), DafnyChar(char::from_u32(54).unwrap()) => int!(6), DafnyChar(char::from_u32(55).unwrap()) => int!(7), DafnyChar(char::from_u32(56).unwrap()) => int!(8), DafnyChar(char::from_u32(57).unwrap()) => int!(9)]
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9891,5)
            pub type CharSeq = Sequence<DafnyChar>;

            /// DafnyStandardLibraries-rs.dfy(3285,3)
            pub type digit = DafnyInt;
        }

        /// DafnyStandardLibraries-rs.dfy(9938,3)
        pub mod HexConversion {
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::seq;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::itertools::Itertools;
            pub use ::std::rc::Rc;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::euclidian_modulo;
            pub use ::dafny_runtime::euclidian_division;
            pub use ::dafny_runtime::string_of;
            pub use ::dafny_runtime::Map;
            pub use ::dafny_runtime::map;
            pub use ::std::primitive::char;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(9787,5)
                pub fn BASE() -> nat {
                    crate::Std::Strings::HexConversion::_default::base()
                }
                /// DafnyStandardLibraries-rs.dfy(9792,5)
                pub fn IsDigitChar(c: &DafnyChar) -> bool {
                    crate::Std::Strings::HexConversion::_default::charToDigit().contains(c)
                }
                /// DafnyStandardLibraries-rs.dfy(9797,5)
                pub fn OfDigits(digits: &Sequence<crate::Std::Strings::HexConversion::digit>) -> Sequence<DafnyChar> {
                    let mut _accumulator: Sequence<DafnyChar> = seq![] as Sequence<DafnyChar>;
                    let mut _r0 = digits.clone();
                    'TAIL_CALL_START: loop {
                        let digits = _r0;
                        if digits.clone().to_array().len() == 0 {
                            return (seq![] as Sequence<DafnyChar>).concat(&_accumulator);
                        } else {
                            _accumulator = seq![crate::Std::Strings::HexConversion::_default::chars().get(&digits.get(&int!(0)))].concat(&_accumulator);
                            let mut _in0: Sequence<crate::Std::Strings::HexConversion::digit> = digits.drop(&int!(1));
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9807,5)
                pub fn OfNat(n: &nat) -> Sequence<DafnyChar> {
                    if n.clone() == int!(0) {
                        seq![crate::Std::Strings::HexConversion::_default::chars().get(&int!(0))]
                    } else {
                        crate::Std::Strings::HexConversion::_default::OfDigits(&crate::Std::Strings::HexConversion::_default::FromNat(n))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9817,5)
                pub fn IsNumberStr(str: &Sequence<DafnyChar>, minus: &DafnyChar) -> bool {
                    !(!(str.clone().to_array().len() == 0)) || (str.get(&int!(0)) == minus.clone() || crate::Std::Strings::HexConversion::_default::charToDigit().contains(&str.get(&int!(0)))) && Itertools::unique((&str.drop(&int!(1))).iter()).all(({
                            let mut str = str.clone();
                            Rc::new(move |__forall_var_0: DafnyChar| -> bool{
            let mut c: DafnyChar = __forall_var_0.clone();
            !str.drop(&int!(1)).contains(&c) || crate::Std::Strings::HexConversion::_default::IsDigitChar(&c)
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                        }).as_ref())
                }
                /// DafnyStandardLibraries-rs.dfy(9825,5)
                pub fn OfInt(n: &DafnyInt, minus: &DafnyChar) -> Sequence<DafnyChar> {
                    if !(n.clone() < int!(0)) {
                        crate::Std::Strings::HexConversion::_default::OfNat(n)
                    } else {
                        seq![minus.clone()].concat(&crate::Std::Strings::HexConversion::_default::OfNat(&(int!(0) - n.clone())))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9835,5)
                pub fn ToNat(str: &Sequence<DafnyChar>) -> nat {
                    if str.clone().to_array().len() == 0 {
                        int!(0)
                    } else {
                        let mut c: DafnyChar = str.get(&(str.cardinality() - int!(1)));
                        crate::Std::Strings::HexConversion::_default::ToNat(&str.take(&(str.cardinality() - int!(1)))) * crate::Std::Strings::HexConversion::_default::base() + crate::Std::Strings::HexConversion::_default::charToDigit().get(&c)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9875,5)
                pub fn ToInt(str: &Sequence<DafnyChar>, minus: &DafnyChar) -> DafnyInt {
                    if seq![minus.clone()] <= str.clone() {
                        int!(0) - crate::Std::Strings::HexConversion::_default::ToNat(&str.drop(&int!(1)))
                    } else {
                        crate::Std::Strings::HexConversion::_default::ToNat(str)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(2728,3)
                pub fn ToNatRight(xs: &Sequence<crate::Std::Strings::HexConversion::digit>) -> nat {
                    if xs.cardinality() == int!(0) {
                        int!(0)
                    } else {
                        crate::Std::Strings::HexConversion::_default::ToNatRight(&crate::Std::Collections::Seq::_default::DropFirst::<crate::Std::Strings::HexConversion::digit>(xs)) * crate::Std::Strings::HexConversion::_default::BASE() + crate::Std::Collections::Seq::_default::First::<crate::Std::Strings::HexConversion::digit>(xs)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(2736,3)
                pub fn ToNatLeft(xs: &Sequence<crate::Std::Strings::HexConversion::digit>) -> nat {
                    let mut _accumulator: nat = int!(0);
                    let mut _r0 = xs.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        if xs.cardinality() == int!(0) {
                            return int!(0) + _accumulator.clone();
                        } else {
                            _accumulator = crate::Std::Collections::Seq::_default::Last::<DafnyInt>(&xs) * crate::Std::Arithmetic::Power::_default::Pow(&crate::Std::Strings::HexConversion::_default::BASE(), &(xs.cardinality() - int!(1))) + _accumulator.clone();
                            let mut _in0: Sequence<crate::Std::Strings::HexConversion::digit> = crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::HexConversion::digit>(&xs);
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3020,3)
                pub fn FromNat(n: &nat) -> Sequence<crate::Std::Strings::HexConversion::digit> {
                    let mut _accumulator: Sequence<crate::Std::Strings::HexConversion::digit> = seq![] as Sequence<crate::Std::Strings::HexConversion::digit>;
                    let mut _r0 = n.clone();
                    'TAIL_CALL_START: loop {
                        let n = _r0;
                        if n.clone() == int!(0) {
                            return _accumulator.concat(&(seq![] as Sequence<DafnyInt>));
                        } else {
                            _accumulator = _accumulator.concat(&seq![euclidian_modulo(n.clone(), crate::Std::Strings::HexConversion::_default::BASE())]);
                            let mut _in0: DafnyInt = euclidian_division(n.clone(), crate::Std::Strings::HexConversion::_default::BASE());
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3104,3)
                pub fn SeqExtend(xs: &Sequence<crate::Std::Strings::HexConversion::digit>, n: &nat) -> Sequence<crate::Std::Strings::HexConversion::digit> {
                    let mut _r0 = xs.clone();
                    let mut _r1 = n.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        let n = _r1;
                        if !(xs.cardinality() < n.clone()) {
                            return xs.clone();
                        } else {
                            let mut _in0: Sequence<crate::Std::Strings::HexConversion::digit> = xs.concat(&seq![int!(0)]);
                            let mut _in1: nat = n.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3116,3)
                pub fn SeqExtendMultiple(xs: &Sequence<crate::Std::Strings::HexConversion::digit>, n: &nat) -> Sequence<crate::Std::Strings::HexConversion::digit> {
                    let mut newLen: DafnyInt = xs.cardinality() + n.clone() - euclidian_modulo(xs.cardinality(), n.clone());
                    crate::Std::Strings::HexConversion::_default::SeqExtend(xs, &newLen)
                }
                /// DafnyStandardLibraries-rs.dfy(3130,3)
                pub fn FromNatWithLen(n: &nat, len: &nat) -> Sequence<crate::Std::Strings::HexConversion::digit> {
                    crate::Std::Strings::HexConversion::_default::SeqExtend(&crate::Std::Strings::HexConversion::_default::FromNat(n), len)
                }
                /// DafnyStandardLibraries-rs.dfy(3153,3)
                pub fn SeqZero(len: &nat) -> Sequence<crate::Std::Strings::HexConversion::digit> {
                    let mut xs: Sequence<crate::Std::Strings::HexConversion::digit> = crate::Std::Strings::HexConversion::_default::FromNatWithLen(&int!(0), len);
                    xs.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(3182,3)
                pub fn SeqAdd(xs: &Sequence<crate::Std::Strings::HexConversion::digit>, ys: &Sequence<crate::Std::Strings::HexConversion::digit>) -> (Sequence<crate::Std::Strings::HexConversion::digit>, nat) {
                    if xs.cardinality() == int!(0) {
                        (
                            seq![] as Sequence<DafnyInt>,
                            int!(0)
                        )
                    } else {
                        let mut __let_tmp_rhs0: (Sequence<crate::Std::Strings::HexConversion::digit>, nat) = crate::Std::Strings::HexConversion::_default::SeqAdd(&crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::HexConversion::digit>(xs), &crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::HexConversion::digit>(ys));
                        let mut _zs_k: Sequence<crate::Std::Strings::HexConversion::digit> = __let_tmp_rhs0.0.clone();
                        let mut cin: nat = __let_tmp_rhs0.1.clone();
                        let mut sum: DafnyInt = crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) + crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) + cin.clone();
                        let mut __let_tmp_rhs1: (DafnyInt, DafnyInt) = if sum.clone() < crate::Std::Strings::HexConversion::_default::BASE() {
                                (
                                    sum.clone(),
                                    int!(0)
                                )
                            } else {
                                (
                                    sum.clone() - crate::Std::Strings::HexConversion::_default::BASE(),
                                    int!(1)
                                )
                            };
                        let mut sum_out: DafnyInt = __let_tmp_rhs1.0.clone();
                        let mut cout: DafnyInt = __let_tmp_rhs1.1.clone();
                        (
                            _zs_k.concat(&seq![sum_out.clone()]),
                            cout.clone()
                        )
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3229,3)
                pub fn SeqSub(xs: &Sequence<crate::Std::Strings::HexConversion::digit>, ys: &Sequence<crate::Std::Strings::HexConversion::digit>) -> (Sequence<crate::Std::Strings::HexConversion::digit>, nat) {
                    if xs.cardinality() == int!(0) {
                        (
                            seq![] as Sequence<DafnyInt>,
                            int!(0)
                        )
                    } else {
                        let mut __let_tmp_rhs0: (Sequence<crate::Std::Strings::HexConversion::digit>, nat) = crate::Std::Strings::HexConversion::_default::SeqSub(&crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::HexConversion::digit>(xs), &crate::Std::Collections::Seq::_default::DropLast::<crate::Std::Strings::HexConversion::digit>(ys));
                        let mut zs: Sequence<crate::Std::Strings::HexConversion::digit> = __let_tmp_rhs0.0.clone();
                        let mut cin: nat = __let_tmp_rhs0.1.clone();
                        let mut __let_tmp_rhs1: (DafnyInt, DafnyInt) = if !(crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) < crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) + cin.clone()) {
                                (
                                    crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) - crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) - cin.clone(),
                                    int!(0)
                                )
                            } else {
                                (
                                    crate::Std::Strings::HexConversion::_default::BASE() + crate::Std::Collections::Seq::_default::Last::<crate::Std::Strings::HexConversion::digit>(xs) - crate::Std::Collections::Seq::_default::Last::<crate::Std::Strings::HexConversion::digit>(ys) - cin.clone(),
                                    int!(1)
                                )
                            };
                        let mut diff_out: DafnyInt = __let_tmp_rhs1.0.clone();
                        let mut cout: DafnyInt = __let_tmp_rhs1.1.clone();
                        (
                            zs.concat(&seq![diff_out.clone()]),
                            cout.clone()
                        )
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(9940,5)
                pub fn HEX_DIGITS() -> Sequence<DafnyChar> {
                    string_of("0123456789ABCDEF")
                }
                /// DafnyStandardLibraries-rs.dfy(9941,5)
                pub fn chars() -> Sequence<DafnyChar> {
                    crate::Std::Strings::HexConversion::_default::HEX_DIGITS()
                }
                /// DafnyStandardLibraries-rs.dfy(9781,5)
                pub fn base() -> DafnyInt {
                    crate::Std::Strings::HexConversion::_default::chars().cardinality()
                }
                /// DafnyStandardLibraries-rs.dfy(9942,5)
                pub fn charToDigit() -> Map<DafnyChar, crate::Std::Strings::HexConversion::digit> {
                    map![DafnyChar(char::from_u32(48).unwrap()) => int!(0), DafnyChar(char::from_u32(49).unwrap()) => int!(1), DafnyChar(char::from_u32(50).unwrap()) => int!(2), DafnyChar(char::from_u32(51).unwrap()) => int!(3), DafnyChar(char::from_u32(52).unwrap()) => int!(4), DafnyChar(char::from_u32(53).unwrap()) => int!(5), DafnyChar(char::from_u32(54).unwrap()) => int!(6), DafnyChar(char::from_u32(55).unwrap()) => int!(7), DafnyChar(char::from_u32(56).unwrap()) => int!(8), DafnyChar(char::from_u32(57).unwrap()) => int!(9), DafnyChar(char::from_u32(97).unwrap()) => int!(10), DafnyChar(char::from_u32(98).unwrap()) => int!(11), DafnyChar(char::from_u32(99).unwrap()) => int!(12), DafnyChar(char::from_u32(100).unwrap()) => int!(13), DafnyChar(char::from_u32(101).unwrap()) => int!(14), DafnyChar(char::from_u32(102).unwrap()) => int!(15), DafnyChar(char::from_u32(65).unwrap()) => int!(10), DafnyChar(char::from_u32(66).unwrap()) => int!(11), DafnyChar(char::from_u32(67).unwrap()) => int!(12), DafnyChar(char::from_u32(68).unwrap()) => int!(13), DafnyChar(char::from_u32(69).unwrap()) => int!(14), DafnyChar(char::from_u32(70).unwrap()) => int!(15)]
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9891,5)
            pub type CharSeq = Sequence<DafnyChar>;

            /// DafnyStandardLibraries-rs.dfy(3285,3)
            pub type digit = DafnyInt;
        }
    }

    /// DafnyStandardLibraries-rs.dfy(10001,1)
    pub mod Unicode {
        /// DafnyStandardLibraries-rs.dfy(9969,1)
        pub mod Base {
            pub use ::dafny_runtime::truncate;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::Set;
            pub use ::dafny_runtime::set;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(9976,3)
                pub fn IsInAssignedPlane(i: crate::Std::Unicode::Base::CodePoint) -> bool {
                    let mut plane: u8 = (i >> truncate!(int!(16), u8)) as u8;
                    crate::Std::Unicode::Base::_default::ASSIGNED_PLANES().contains(&plane)
                }
                /// DafnyStandardLibraries-rs.dfy(9970,3)
                pub fn HIGH_SURROGATE_MIN() -> crate::Std::Unicode::Base::CodePoint {
                    55296 as u32
                }
                /// DafnyStandardLibraries-rs.dfy(9971,3)
                pub fn HIGH_SURROGATE_MAX() -> crate::Std::Unicode::Base::CodePoint {
                    56319 as u32
                }
                /// DafnyStandardLibraries-rs.dfy(9972,3)
                pub fn LOW_SURROGATE_MIN() -> crate::Std::Unicode::Base::CodePoint {
                    56320 as u32
                }
                /// DafnyStandardLibraries-rs.dfy(9973,3)
                pub fn LOW_SURROGATE_MAX() -> crate::Std::Unicode::Base::CodePoint {
                    57343 as u32
                }
                /// DafnyStandardLibraries-rs.dfy(9974,3)
                pub fn ASSIGNED_PLANES() -> Set<u8> {
                    set!{0 as u8, 1 as u8, 2 as u8, 3 as u8, 14 as u8, 15 as u8, 16 as u8}
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9982,3)
            pub type CodePoint = u32;

            /// DafnyStandardLibraries-rs.dfy(9985,3)
            pub type HighSurrogateCodePoint = u32;

            /// An element of HighSurrogateCodePoint
            pub fn __init_HighSurrogateCodePoint() -> u32 {
                crate::Std::Unicode::Base::_default::HIGH_SURROGATE_MIN()
            }

            /// DafnyStandardLibraries-rs.dfy(9989,3)
            pub type LowSurrogateCodePoint = u32;

            /// An element of LowSurrogateCodePoint
            pub fn __init_LowSurrogateCodePoint() -> u32 {
                crate::Std::Unicode::Base::_default::LOW_SURROGATE_MIN()
            }

            /// DafnyStandardLibraries-rs.dfy(9993,3)
            pub type ScalarValue = u32;

            /// DafnyStandardLibraries-rs.dfy(9996,3)
            pub type AssignedCodePoint = u32;
        }

        /// DafnyStandardLibraries-rs.dfy(10269,1)
        pub mod UnicodeStringsWithUnicodeChar {
            pub use ::dafny_runtime::DafnyChar;
            pub use crate::Std::Unicode::Base::ScalarValue;
            pub use ::dafny_runtime::truncate;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::NumCast;
            pub use ::dafny_runtime::Sequence;
            pub use ::std::rc::Rc;
            pub use crate::Std::Wrappers::Option;
            pub use crate::Std::Wrappers::Result;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(10289,3)
                pub fn CharAsUnicodeScalarValue(c: &DafnyChar) -> ScalarValue {
                    truncate!(int!(c.clone().0), u32)
                }
                /// DafnyStandardLibraries-rs.dfy(10295,3)
                pub fn CharFromUnicodeScalarValue(sv: ScalarValue) -> DafnyChar {
                    DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(sv)).unwrap()).unwrap())
                }
                /// DafnyStandardLibraries-rs.dfy(10301,3)
                pub fn ToUTF8Checked(s: &Sequence<DafnyChar>) -> Rc<Option<Sequence<u8>>> {
                    let mut asCodeUnits: Sequence<ScalarValue> = crate::Std::Collections::Seq::_default::Map::<DafnyChar, ScalarValue>(&(Rc::new(move |x0: &DafnyChar| crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::CharAsUnicodeScalarValue(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>), s);
                    let mut asUtf8CodeUnits: crate::Std::Unicode::Utf8EncodingForm::WellFormedCodeUnitSeq = crate::Std::Unicode::Utf8EncodingForm::_default::EncodeScalarSequence(&asCodeUnits);
                    let mut asBytes: Sequence<u8> = crate::Std::Collections::Seq::_default::Map::<u8, u8>(&({
                                Rc::new(move |cu: &u8| -> u8{
            cu.clone() as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }), &asUtf8CodeUnits);
                    Rc::new(Option::Some::<Sequence<u8>> {
                            value: asBytes.clone()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(10310,3)
                pub fn FromUTF8Checked(bs: &Sequence<u8>) -> Rc<Result<Sequence<DafnyChar>, Sequence<DafnyChar>>> {
                    let mut asCodeUnits: Sequence<u8> = crate::Std::Collections::Seq::_default::Map::<u8, u8>(&({
                                Rc::new(move |c: &u8| -> u8{
            c.clone() as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }), bs);
                    let mut valueOrError0: Rc<Result<Sequence<ScalarValue>, Sequence<DafnyChar>>> = crate::Std::Unicode::Utf8EncodingForm::_default::DecodeCodeUnitSequenceChecked(&asCodeUnits);
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Sequence<DafnyChar>>()
                    } else {
                        let mut utf32: Sequence<ScalarValue> = valueOrError0.Extract();
                        let mut asChars: Sequence<DafnyChar> = crate::Std::Collections::Seq::_default::Map::<ScalarValue, DafnyChar>(&(Rc::new(move |x0: &ScalarValue| crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::CharFromUnicodeScalarValue(x0.clone())) as Rc<dyn ::std::ops::Fn(&_) -> _>), &utf32);
                        Rc::new(Result::Success::<Sequence<DafnyChar>, Sequence<DafnyChar>> {
                                value: asChars.clone()
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10316,3)
                pub fn ToUTF16Checked(s: &Sequence<DafnyChar>) -> Rc<Option<Sequence<u16>>> {
                    let mut asCodeUnits: Sequence<ScalarValue> = crate::Std::Collections::Seq::_default::Map::<DafnyChar, ScalarValue>(&(Rc::new(move |x0: &DafnyChar| crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::CharAsUnicodeScalarValue(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>), s);
                    let mut asUtf16CodeUnits: crate::Std::Unicode::Utf16EncodingForm::WellFormedCodeUnitSeq = crate::Std::Unicode::Utf16EncodingForm::_default::EncodeScalarSequence(&asCodeUnits);
                    let mut asBytes: Sequence<u16> = crate::Std::Collections::Seq::_default::Map::<u16, u16>(&({
                                Rc::new(move |cu: &u16| -> u16{
            cu.clone() as u16
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }), &asUtf16CodeUnits);
                    Rc::new(Option::Some::<Sequence<u16>> {
                            value: asBytes.clone()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(10325,3)
                pub fn FromUTF16Checked(bs: &Sequence<u16>) -> Rc<Result<Sequence<DafnyChar>, Sequence<DafnyChar>>> {
                    let mut asCodeUnits: Sequence<u16> = crate::Std::Collections::Seq::_default::Map::<u16, u16>(&({
                                Rc::new(move |c: &u16| -> u16{
            c.clone() as u16
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }), bs);
                    let mut valueOrError0: Rc<Result<Sequence<ScalarValue>, Sequence<DafnyChar>>> = crate::Std::Unicode::Utf16EncodingForm::_default::DecodeCodeUnitSequenceChecked(&asCodeUnits);
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Sequence<DafnyChar>>()
                    } else {
                        let mut utf32: Sequence<ScalarValue> = valueOrError0.Extract();
                        let mut asChars: Sequence<DafnyChar> = crate::Std::Collections::Seq::_default::Map::<ScalarValue, DafnyChar>(&(Rc::new(move |x0: &ScalarValue| crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::CharFromUnicodeScalarValue(x0.clone())) as Rc<dyn ::std::ops::Fn(&_) -> _>), &utf32);
                        Rc::new(Result::Success::<Sequence<DafnyChar>, Sequence<DafnyChar>> {
                                value: asChars.clone()
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10244,3)
                pub fn ASCIIToUTF8(s: &Sequence<DafnyChar>) -> Sequence<u8> {
                    crate::Std::Collections::Seq::_default::Map::<DafnyChar, u8>(&({
                            Rc::new(move |c: &DafnyChar| -> u8{
            c.clone().0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), s)
                }
                /// DafnyStandardLibraries-rs.dfy(10254,3)
                pub fn ASCIIToUTF16(s: &Sequence<DafnyChar>) -> Sequence<u16> {
                    crate::Std::Collections::Seq::_default::Map::<DafnyChar, u16>(&({
                            Rc::new(move |c: &DafnyChar| -> u16{
            c.clone().0 as u16
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), s)
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(10338,1)
        pub mod Utf16EncodingForm {
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::int;
            pub use ::std::rc::Rc;
            pub use crate::Std::Wrappers::Option;
            pub use crate::Std::Unicode::Base::ScalarValue;
            pub use ::dafny_runtime::seq;
            pub use ::dafny_runtime::truncate;
            pub use crate::Std::Wrappers::Result;
            pub use ::dafny_runtime::MaybePlacebo;
            pub use crate::Std::Wrappers::Result::Success;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::integer_range_down;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::dafny_runtime::string_of;
            pub use crate::Std::Wrappers::Result::Failure;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(10339,3)
                pub fn IsMinimalWellFormedCodeUnitSubsequence(s: &Sequence<u16>) -> bool {
                    if s.cardinality() == int!(1) {
                        crate::Std::Unicode::Utf16EncodingForm::_default::IsWellFormedSingleCodeUnitSequence(s)
                    } else {
                        if s.cardinality() == int!(2) {
                            let mut b: bool = crate::Std::Unicode::Utf16EncodingForm::_default::IsWellFormedDoubleCodeUnitSequence(s);
                            b
                        } else {
                            false
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10351,3)
                pub fn IsWellFormedSingleCodeUnitSequence(s: &Sequence<u16>) -> bool {
                    let mut firstWord: u16 = s.get(&int!(0));
                    !(firstWord < 0 as u16) && !((55295 as u16) < firstWord) || !(firstWord < 57344 as u16) && !((65535 as u16) < firstWord)
                }
                /// DafnyStandardLibraries-rs.dfy(10358,3)
                pub fn IsWellFormedDoubleCodeUnitSequence(s: &Sequence<u16>) -> bool {
                    let mut firstWord: u16 = s.get(&int!(0));
                    let mut secondWord: u16 = s.get(&int!(1));
                    !(firstWord < 55296 as u16) && !((56319 as u16) < firstWord) && (!(secondWord < 56320 as u16) && !((57343 as u16) < secondWord))
                }
                /// DafnyStandardLibraries-rs.dfy(10368,3)
                pub fn SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: &Sequence<u16>) -> Rc<Option<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq>> {
                    if !(s.cardinality() < int!(1)) && crate::Std::Unicode::Utf16EncodingForm::_default::IsWellFormedSingleCodeUnitSequence(&s.take(&int!(1))) {
                        Rc::new(Option::Some::<Sequence<u16>> {
                                value: s.take(&int!(1))
                            })
                    } else {
                        if !(s.cardinality() < int!(2)) && crate::Std::Unicode::Utf16EncodingForm::_default::IsWellFormedDoubleCodeUnitSequence(&s.take(&int!(2))) {
                            Rc::new(Option::Some::<Sequence<u16>> {
                                    value: s.take(&int!(2))
                                })
                        } else {
                            Rc::new(Option::None::<Sequence<u16>> {})
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10381,3)
                pub fn EncodeScalarValue(v: ScalarValue) -> crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq {
                    if !(v < 0 as u32) && !((55295 as u32) < v) || !(v < 57344 as u32) && !((65535 as u32) < v) {
                        crate::Std::Unicode::Utf16EncodingForm::_default::EncodeScalarValueSingleWord(v)
                    } else {
                        crate::Std::Unicode::Utf16EncodingForm::_default::EncodeScalarValueDoubleWord(v)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10389,3)
                pub fn EncodeScalarValueSingleWord(v: ScalarValue) -> crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq {
                    let mut firstWord: u16 = v as u16;
                    seq![firstWord]
                }
                /// DafnyStandardLibraries-rs.dfy(10398,3)
                pub fn EncodeScalarValueDoubleWord(v: ScalarValue) -> crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq {
                    let mut x2: u16 = (v & 1023 as u32) as u16;
                    let mut x1: u8 = ((v & 64512 as u32) >> truncate!(int!(10), u8)) as u8;
                    let mut u: u8 = ((v & 2031616 as u32) >> truncate!(int!(16), u8)) as u8;
                    let mut w: u8 = u.wrapping_sub(1 as u8);
                    let mut firstWord: u16 = 55296 as u16 | (w as u16) << truncate!(int!(6), u8) | x1 as u16;
                    let mut secondWord: u16 = 56320 as u16 | x2;
                    seq![firstWord, secondWord]
                }
                /// DafnyStandardLibraries-rs.dfy(10412,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequence(m: &crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    if m.cardinality() == int!(1) {
                        crate::Std::Unicode::Utf16EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m)
                    } else {
                        crate::Std::Unicode::Utf16EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10420,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m: &crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstWord: u16 = m.get(&int!(0));
                    let mut x: u16 = firstWord;
                    x as u32
                }
                /// DafnyStandardLibraries-rs.dfy(10431,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m: &crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstWord: u16 = m.get(&int!(0));
                    let mut secondWord: u16 = m.get(&int!(1));
                    let mut x2: u32 = (secondWord & 1023 as u16) as u32;
                    let mut x1: u32 = (firstWord & 63 as u16) as u32;
                    let mut w: u32 = ((firstWord & 960 as u16) >> truncate!(int!(6), u8)) as u32;
                    let mut u: u32 = w.wrapping_add(1 as u32);
                    let mut v: u32 = u << truncate!(int!(16), u8) | x1 << truncate!(int!(10), u8) | x2;
                    v
                }
                /// DafnyStandardLibraries-rs.dfy(10053,3)
                pub fn PartitionCodeUnitSequenceChecked(s: &Sequence<u16>) -> Rc<Result<Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u16>>> {
                    let mut maybeParts = MaybePlacebo::<Rc<Result<Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u16>>>>::new();
                    if s.clone().to_array().len() == 0 {
                        maybeParts = MaybePlacebo::from(Rc::new(Result::Success::<Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u16>> {
                                        value: seq![] as Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq>
                                    }));
                        return maybeParts.read();
                    };
                    let mut result: Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq> = seq![] as Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq>;
                    let mut rest: Sequence<u16> = s.clone();
                    while int!(0) < rest.cardinality() {
                        let mut valueOrError0: Rc<Result<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq, Sequence<u16>>> = crate::Std::Unicode::Utf16EncodingForm::_default::SplitPrefixMinimalWellFormedCodeUnitSubsequence(&rest).ToResult::<Sequence<u16>>(&rest);
                        if valueOrError0.IsFailure() {
                            maybeParts = MaybePlacebo::from(valueOrError0.PropagateFailure::<Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq>>());
                            return maybeParts.read();
                        };
                        let mut prefix: crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq = valueOrError0.Extract();
                        result = result.concat(&seq![prefix.clone()]);
                        rest = rest.drop(&prefix.cardinality());
                    };
                    maybeParts = MaybePlacebo::from(Rc::new(Result::Success::<Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u16>> {
                                    value: result.clone()
                                }));
                    return maybeParts.read();
                }
                /// DafnyStandardLibraries-rs.dfy(10079,3)
                pub fn PartitionCodeUnitSequence(s: &crate::Std::Unicode::Utf16EncodingForm::WellFormedCodeUnitSeq) -> Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq> {
                    crate::Std::Unicode::Utf16EncodingForm::_default::PartitionCodeUnitSequenceChecked(s).Extract()
                }
                /// DafnyStandardLibraries-rs.dfy(10107,3)
                pub fn IsWellFormedCodeUnitSequence(s: &Sequence<u16>) -> bool {
                    matches!((&crate::Std::Unicode::Utf16EncodingForm::_default::PartitionCodeUnitSequenceChecked(s)).as_ref(), Success{ .. })
                }
                /// DafnyStandardLibraries-rs.dfy(10148,3)
                pub fn EncodeScalarSequence(vs: &Sequence<ScalarValue>) -> crate::Std::Unicode::Utf16EncodingForm::WellFormedCodeUnitSeq {
                    let mut s: crate::Std::Unicode::Utf16EncodingForm::WellFormedCodeUnitSeq = seq![] as Sequence<u16>;
                    s = seq![] as Sequence<u16>;
                    let mut _lo0: DafnyInt = int!(0);
                    for i in integer_range_down(vs.cardinality(), _lo0.clone()) {
                        let mut next: crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq = crate::Std::Unicode::Utf16EncodingForm::_default::EncodeScalarValue(vs.get(&i));
                        s = next.concat(&s);
                    }
                    return s.clone();
                }
                /// DafnyStandardLibraries-rs.dfy(10167,3)
                pub fn DecodeCodeUnitSequence(s: &crate::Std::Unicode::Utf16EncodingForm::WellFormedCodeUnitSeq) -> Sequence<ScalarValue> {
                    let mut parts: Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq> = crate::Std::Unicode::Utf16EncodingForm::_default::PartitionCodeUnitSequence(s);
                    let mut vs: Sequence<ScalarValue> = crate::Std::Collections::Seq::_default::MapPartialFunction::<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq, ScalarValue>(&(Rc::new(move |x0: &crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq| crate::Std::Unicode::Utf16EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequence(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>), &parts);
                    vs.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(10184,3)
                pub fn DecodeErrorMessage(index: &DafnyInt) -> Sequence<DafnyChar> {
                    string_of("Could not decode byte at index ").concat(&crate::Std::Strings::_default::OfInt(index))
                }
                /// DafnyStandardLibraries-rs.dfy(10189,3)
                pub fn DecodeCodeUnitSequenceChecked(s: &Sequence<u16>) -> Rc<Result<Sequence<ScalarValue>, Sequence<DafnyChar>>> {
                    let mut resultVs = MaybePlacebo::<Rc<Result<Sequence<ScalarValue>, Sequence<DafnyChar>>>>::new();
                    let mut maybeParts: Rc<Result<Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u16>>> = crate::Std::Unicode::Utf16EncodingForm::_default::PartitionCodeUnitSequenceChecked(s);
                    if matches!((&maybeParts).as_ref(), Failure{ .. }) {
                        resultVs = MaybePlacebo::from(Rc::new(Result::Failure::<Sequence<ScalarValue>, Sequence<DafnyChar>> {
                                        error: crate::Std::Unicode::Utf16EncodingForm::_default::DecodeErrorMessage(&(s.cardinality() - maybeParts.error().cardinality()))
                                    }));
                        return resultVs.read();
                    };
                    let mut parts: Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq> = maybeParts.value().clone();
                    let mut vs: Sequence<ScalarValue> = crate::Std::Collections::Seq::_default::MapPartialFunction::<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq, ScalarValue>(&(Rc::new(move |x0: &crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq| crate::Std::Unicode::Utf16EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequence(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>), &parts);
                    resultVs = MaybePlacebo::from(Rc::new(Result::Success::<Sequence<ScalarValue>, Sequence<DafnyChar>> {
                                    value: vs.clone()
                                }));
                    return resultVs.read();
                }
            }

            /// DafnyStandardLibraries-rs.dfy(10230,3)
            pub type WellFormedCodeUnitSeq = Sequence<u16>;

            /// An element of WellFormedCodeUnitSeq
            pub fn __init_WellFormedCodeUnitSeq() -> Sequence<u16> {
                seq![] as Sequence<u16>
            }

            /// DafnyStandardLibraries-rs.dfy(10234,3)
            pub type MinimalWellFormedCodeUnitSeq = Sequence<u16>;
        }

        /// DafnyStandardLibraries-rs.dfy(10451,1)
        pub mod Utf8EncodingForm {
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::int;
            pub use ::std::rc::Rc;
            pub use crate::Std::Wrappers::Option;
            pub use crate::Std::Unicode::Base::ScalarValue;
            pub use ::dafny_runtime::seq;
            pub use ::dafny_runtime::truncate;
            pub use crate::Std::Wrappers::Result;
            pub use ::dafny_runtime::MaybePlacebo;
            pub use crate::Std::Wrappers::Result::Success;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::integer_range_down;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::dafny_runtime::string_of;
            pub use crate::Std::Wrappers::Result::Failure;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(10452,3)
                pub fn IsMinimalWellFormedCodeUnitSubsequence(s: &Sequence<u8>) -> bool {
                    if s.cardinality() == int!(1) {
                        let mut b: bool = crate::Std::Unicode::Utf8EncodingForm::_default::IsWellFormedSingleCodeUnitSequence(s);
                        b
                    } else {
                        if s.cardinality() == int!(2) {
                            let mut b: bool = crate::Std::Unicode::Utf8EncodingForm::_default::IsWellFormedDoubleCodeUnitSequence(s);
                            b
                        } else {
                            if s.cardinality() == int!(3) {
                                let mut b: bool = crate::Std::Unicode::Utf8EncodingForm::_default::IsWellFormedTripleCodeUnitSequence(s);
                                b
                            } else {
                                if s.cardinality() == int!(4) {
                                    let mut b: bool = crate::Std::Unicode::Utf8EncodingForm::_default::IsWellFormedQuadrupleCodeUnitSequence(s);
                                    b
                                } else {
                                    false
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10474,3)
                pub fn IsWellFormedSingleCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    let mut firstByte: u8 = s.get(&int!(0));
                    true && (!(firstByte < 0 as u8) && !((127 as u8) < firstByte))
                }
                /// DafnyStandardLibraries-rs.dfy(10482,3)
                pub fn IsWellFormedDoubleCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    let mut firstByte: u8 = s.get(&int!(0));
                    let mut secondByte: u8 = s.get(&int!(1));
                    !(firstByte < 194 as u8) && !((223 as u8) < firstByte) && (!(secondByte < 128 as u8) && !((191 as u8) < secondByte))
                }
                /// DafnyStandardLibraries-rs.dfy(10492,3)
                pub fn IsWellFormedTripleCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    let mut firstByte: u8 = s.get(&int!(0));
                    let mut secondByte: u8 = s.get(&int!(1));
                    let mut thirdByte: u8 = s.get(&int!(2));
                    (firstByte == 224 as u8 && (!(secondByte < 160 as u8) && !((191 as u8) < secondByte)) || !(firstByte < 225 as u8) && !((236 as u8) < firstByte) && (!(secondByte < 128 as u8) && !((191 as u8) < secondByte)) || firstByte == 237 as u8 && (!(secondByte < 128 as u8) && !((159 as u8) < secondByte)) || !(firstByte < 238 as u8) && !((239 as u8) < firstByte) && (!(secondByte < 128 as u8) && !((191 as u8) < secondByte))) && (!(thirdByte < 128 as u8) && !((191 as u8) < thirdByte))
                }
                /// DafnyStandardLibraries-rs.dfy(10503,3)
                pub fn IsWellFormedQuadrupleCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    let mut firstByte: u8 = s.get(&int!(0));
                    let mut secondByte: u8 = s.get(&int!(1));
                    let mut thirdByte: u8 = s.get(&int!(2));
                    let mut fourthByte: u8 = s.get(&int!(3));
                    (firstByte == 240 as u8 && (!(secondByte < 144 as u8) && !((191 as u8) < secondByte)) || !(firstByte < 241 as u8) && !((243 as u8) < firstByte) && (!(secondByte < 128 as u8) && !((191 as u8) < secondByte)) || firstByte == 244 as u8 && (!(secondByte < 128 as u8) && !((143 as u8) < secondByte))) && (!(thirdByte < 128 as u8) && !((191 as u8) < thirdByte)) && (!(fourthByte < 128 as u8) && !((191 as u8) < fourthByte))
                }
                /// DafnyStandardLibraries-rs.dfy(10516,3)
                pub fn SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: &Sequence<u8>) -> Rc<Option<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq>> {
                    if !(s.cardinality() < int!(1)) && crate::Std::Unicode::Utf8EncodingForm::_default::IsWellFormedSingleCodeUnitSequence(&s.take(&int!(1))) {
                        Rc::new(Option::Some::<Sequence<u8>> {
                                value: s.take(&int!(1))
                            })
                    } else {
                        if !(s.cardinality() < int!(2)) && crate::Std::Unicode::Utf8EncodingForm::_default::IsWellFormedDoubleCodeUnitSequence(&s.take(&int!(2))) {
                            Rc::new(Option::Some::<Sequence<u8>> {
                                    value: s.take(&int!(2))
                                })
                        } else {
                            if !(s.cardinality() < int!(3)) && crate::Std::Unicode::Utf8EncodingForm::_default::IsWellFormedTripleCodeUnitSequence(&s.take(&int!(3))) {
                                Rc::new(Option::Some::<Sequence<u8>> {
                                        value: s.take(&int!(3))
                                    })
                            } else {
                                if !(s.cardinality() < int!(4)) && crate::Std::Unicode::Utf8EncodingForm::_default::IsWellFormedQuadrupleCodeUnitSequence(&s.take(&int!(4))) {
                                    Rc::new(Option::Some::<Sequence<u8>> {
                                            value: s.take(&int!(4))
                                        })
                                } else {
                                    Rc::new(Option::None::<Sequence<u8>> {})
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10530,3)
                pub fn EncodeScalarValue(v: ScalarValue) -> crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq {
                    if !((127 as u32) < v) {
                        crate::Std::Unicode::Utf8EncodingForm::_default::EncodeScalarValueSingleByte(v)
                    } else {
                        if !((2047 as u32) < v) {
                            crate::Std::Unicode::Utf8EncodingForm::_default::EncodeScalarValueDoubleByte(v)
                        } else {
                            if !((65535 as u32) < v) {
                                crate::Std::Unicode::Utf8EncodingForm::_default::EncodeScalarValueTripleByte(v)
                            } else {
                                crate::Std::Unicode::Utf8EncodingForm::_default::EncodeScalarValueQuadrupleByte(v)
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10542,3)
                pub fn EncodeScalarValueSingleByte(v: ScalarValue) -> crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq {
                    let mut x: u8 = (v & 127 as u32) as u8;
                    let mut firstByte: u8 = x;
                    seq![firstByte]
                }
                /// DafnyStandardLibraries-rs.dfy(10552,3)
                pub fn EncodeScalarValueDoubleByte(v: ScalarValue) -> Sequence<u8> {
                    let mut x: u8 = (v & 63 as u32) as u8;
                    let mut y: u8 = ((v & 1984 as u32) >> truncate!(int!(6), u8)) as u8;
                    let mut firstByte: u8 = 192 as u8 | y;
                    let mut secondByte: u8 = 128 as u8 | x;
                    seq![firstByte, secondByte]
                }
                /// DafnyStandardLibraries-rs.dfy(10564,3)
                pub fn EncodeScalarValueTripleByte(v: ScalarValue) -> Sequence<u8> {
                    let mut x: u8 = (v & 63 as u32) as u8;
                    let mut y: u8 = ((v & 4032 as u32) >> truncate!(int!(6), u8)) as u8;
                    let mut z: u8 = ((v & 61440 as u32) >> truncate!(int!(12), u8)) as u8;
                    let mut firstByte: u8 = 224 as u8 | z;
                    let mut secondByte: u8 = 128 as u8 | y;
                    let mut thirdByte: u8 = 128 as u8 | x;
                    seq![firstByte, secondByte, thirdByte]
                }
                /// DafnyStandardLibraries-rs.dfy(10578,3)
                pub fn EncodeScalarValueQuadrupleByte(v: ScalarValue) -> Sequence<u8> {
                    let mut x: u8 = (v & 63 as u32) as u8;
                    let mut y: u8 = ((v & 4032 as u32) >> truncate!(int!(6), u8)) as u8;
                    let mut z: u8 = ((v & 61440 as u32) >> truncate!(int!(12), u8)) as u8;
                    let mut u2: u8 = ((v & 196608 as u32) >> truncate!(int!(16), u8)) as u8;
                    let mut u1: u8 = ((v & 1835008 as u32) >> truncate!(int!(18), u8)) as u8;
                    let mut firstByte: u8 = 240 as u8 | u1;
                    let mut secondByte: u8 = 128 as u8 | u2 << truncate!(int!(4), u8) | z;
                    let mut thirdByte: u8 = 128 as u8 | y;
                    let mut fourthByte: u8 = 128 as u8 | x;
                    seq![firstByte, secondByte, thirdByte, fourthByte]
                }
                /// DafnyStandardLibraries-rs.dfy(10596,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequence(m: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    if m.cardinality() == int!(1) {
                        crate::Std::Unicode::Utf8EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m)
                    } else {
                        if m.cardinality() == int!(2) {
                            crate::Std::Unicode::Utf8EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m)
                        } else {
                            if m.cardinality() == int!(3) {
                                crate::Std::Unicode::Utf8EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m)
                            } else {
                                crate::Std::Unicode::Utf8EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m)
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(10608,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstByte: u8 = m.get(&int!(0));
                    let mut x: u8 = firstByte;
                    x as u32
                }
                /// DafnyStandardLibraries-rs.dfy(10618,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstByte: u8 = m.get(&int!(0));
                    let mut secondByte: u8 = m.get(&int!(1));
                    let mut y: u32 = (firstByte & 31 as u8) as u32;
                    let mut x: u32 = (secondByte & 63 as u8) as u32;
                    y << truncate!(int!(6), u8) | x
                }
                /// DafnyStandardLibraries-rs.dfy(10630,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstByte: u8 = m.get(&int!(0));
                    let mut secondByte: u8 = m.get(&int!(1));
                    let mut thirdByte: u8 = m.get(&int!(2));
                    let mut z: u32 = (firstByte & 15 as u8) as u32;
                    let mut y: u32 = (secondByte & 63 as u8) as u32;
                    let mut x: u32 = (thirdByte & 63 as u8) as u32;
                    z << truncate!(int!(12), u8) | y << truncate!(int!(6), u8) | x
                }
                /// DafnyStandardLibraries-rs.dfy(10645,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstByte: u8 = m.get(&int!(0));
                    let mut secondByte: u8 = m.get(&int!(1));
                    let mut thirdByte: u8 = m.get(&int!(2));
                    let mut fourthByte: u8 = m.get(&int!(3));
                    let mut u1: u32 = (firstByte & 7 as u8) as u32;
                    let mut u2: u32 = ((secondByte & 48 as u8) >> truncate!(int!(4), u8)) as u32;
                    let mut z: u32 = (secondByte & 15 as u8) as u32;
                    let mut y: u32 = (thirdByte & 63 as u8) as u32;
                    let mut x: u32 = (fourthByte & 63 as u8) as u32;
                    let mut r: u32 = u1 << truncate!(int!(18), u8) | u2 << truncate!(int!(16), u8) | z << truncate!(int!(12), u8) | y << truncate!(int!(6), u8) | x;
                    r
                }
                /// DafnyStandardLibraries-rs.dfy(10053,3)
                pub fn PartitionCodeUnitSequenceChecked(s: &Sequence<u8>) -> Rc<Result<Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u8>>> {
                    let mut maybeParts = MaybePlacebo::<Rc<Result<Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u8>>>>::new();
                    if s.clone().to_array().len() == 0 {
                        maybeParts = MaybePlacebo::from(Rc::new(Result::Success::<Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u8>> {
                                        value: seq![] as Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq>
                                    }));
                        return maybeParts.read();
                    };
                    let mut result: Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq> = seq![] as Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq>;
                    let mut rest: Sequence<u8> = s.clone();
                    while int!(0) < rest.cardinality() {
                        let mut valueOrError0: Rc<Result<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq, Sequence<u8>>> = crate::Std::Unicode::Utf8EncodingForm::_default::SplitPrefixMinimalWellFormedCodeUnitSubsequence(&rest).ToResult::<Sequence<u8>>(&rest);
                        if valueOrError0.IsFailure() {
                            maybeParts = MaybePlacebo::from(valueOrError0.PropagateFailure::<Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq>>());
                            return maybeParts.read();
                        };
                        let mut prefix: crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq = valueOrError0.Extract();
                        result = result.concat(&seq![prefix.clone()]);
                        rest = rest.drop(&prefix.cardinality());
                    };
                    maybeParts = MaybePlacebo::from(Rc::new(Result::Success::<Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u8>> {
                                    value: result.clone()
                                }));
                    return maybeParts.read();
                }
                /// DafnyStandardLibraries-rs.dfy(10079,3)
                pub fn PartitionCodeUnitSequence(s: &crate::Std::Unicode::Utf8EncodingForm::WellFormedCodeUnitSeq) -> Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq> {
                    crate::Std::Unicode::Utf8EncodingForm::_default::PartitionCodeUnitSequenceChecked(s).Extract()
                }
                /// DafnyStandardLibraries-rs.dfy(10107,3)
                pub fn IsWellFormedCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    matches!((&crate::Std::Unicode::Utf8EncodingForm::_default::PartitionCodeUnitSequenceChecked(s)).as_ref(), Success{ .. })
                }
                /// DafnyStandardLibraries-rs.dfy(10148,3)
                pub fn EncodeScalarSequence(vs: &Sequence<ScalarValue>) -> crate::Std::Unicode::Utf8EncodingForm::WellFormedCodeUnitSeq {
                    let mut s: crate::Std::Unicode::Utf8EncodingForm::WellFormedCodeUnitSeq = seq![] as Sequence<u8>;
                    s = seq![] as Sequence<u8>;
                    let mut _lo0: DafnyInt = int!(0);
                    for i in integer_range_down(vs.cardinality(), _lo0.clone()) {
                        let mut next: crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq = crate::Std::Unicode::Utf8EncodingForm::_default::EncodeScalarValue(vs.get(&i));
                        s = next.concat(&s);
                    }
                    return s.clone();
                }
                /// DafnyStandardLibraries-rs.dfy(10167,3)
                pub fn DecodeCodeUnitSequence(s: &crate::Std::Unicode::Utf8EncodingForm::WellFormedCodeUnitSeq) -> Sequence<ScalarValue> {
                    let mut parts: Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq> = crate::Std::Unicode::Utf8EncodingForm::_default::PartitionCodeUnitSequence(s);
                    let mut vs: Sequence<ScalarValue> = crate::Std::Collections::Seq::_default::MapPartialFunction::<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq, ScalarValue>(&(Rc::new(move |x0: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq| crate::Std::Unicode::Utf8EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequence(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>), &parts);
                    vs.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(10184,3)
                pub fn DecodeErrorMessage(index: &DafnyInt) -> Sequence<DafnyChar> {
                    string_of("Could not decode byte at index ").concat(&crate::Std::Strings::_default::OfInt(index))
                }
                /// DafnyStandardLibraries-rs.dfy(10189,3)
                pub fn DecodeCodeUnitSequenceChecked(s: &Sequence<u8>) -> Rc<Result<Sequence<ScalarValue>, Sequence<DafnyChar>>> {
                    let mut resultVs = MaybePlacebo::<Rc<Result<Sequence<ScalarValue>, Sequence<DafnyChar>>>>::new();
                    let mut maybeParts: Rc<Result<Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq>, Sequence<u8>>> = crate::Std::Unicode::Utf8EncodingForm::_default::PartitionCodeUnitSequenceChecked(s);
                    if matches!((&maybeParts).as_ref(), Failure{ .. }) {
                        resultVs = MaybePlacebo::from(Rc::new(Result::Failure::<Sequence<ScalarValue>, Sequence<DafnyChar>> {
                                        error: crate::Std::Unicode::Utf8EncodingForm::_default::DecodeErrorMessage(&(s.cardinality() - maybeParts.error().cardinality()))
                                    }));
                        return resultVs.read();
                    };
                    let mut parts: Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq> = maybeParts.value().clone();
                    let mut vs: Sequence<ScalarValue> = crate::Std::Collections::Seq::_default::MapPartialFunction::<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq, ScalarValue>(&(Rc::new(move |x0: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq| crate::Std::Unicode::Utf8EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequence(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>), &parts);
                    resultVs = MaybePlacebo::from(Rc::new(Result::Success::<Sequence<ScalarValue>, Sequence<DafnyChar>> {
                                    value: vs.clone()
                                }));
                    return resultVs.read();
                }
            }

            /// DafnyStandardLibraries-rs.dfy(10230,3)
            pub type WellFormedCodeUnitSeq = Sequence<u8>;

            /// An element of WellFormedCodeUnitSeq
            pub fn __init_WellFormedCodeUnitSeq() -> Sequence<u8> {
                seq![] as Sequence<u8>
            }

            /// DafnyStandardLibraries-rs.dfy(10234,3)
            pub type MinimalWellFormedCodeUnitSeq = Sequence<u8>;
        }

        /// DafnyStandardLibraries-rs.dfy(10671,1)
        pub mod Utf8EncodingScheme {
            pub use ::dafny_runtime::Sequence;
            pub use ::std::rc::Rc;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(10672,3)
                pub fn Serialize(s: &Sequence<u8>) -> Sequence<u8> {
                    crate::Std::Collections::Seq::_default::Map::<u8, u8>(&({
                            Rc::new(move |c: &u8| -> u8{
            c.clone() as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), s)
                }
                /// DafnyStandardLibraries-rs.dfy(10677,3)
                pub fn Deserialize(b: &Sequence<u8>) -> Sequence<u8> {
                    crate::Std::Collections::Seq::_default::Map::<u8, u8>(&({
                            Rc::new(move |b: &u8| -> u8{
            b.clone() as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), b)
                }
            }
        }
    }

    /// DafnyStandardLibraries-rs.dfy(10720,1)
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
            /// DafnyStandardLibraries-rs.dfy(10721,3)
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

        /// DafnyStandardLibraries-rs.dfy(10729,3)
        #[derive(Clone)]
        pub enum Option<T: DafnyType> {
            None {},
            Some {
                value: T
            }
        }

        impl<T: DafnyType> Option<T> {
            /// DafnyStandardLibraries-rs.dfy(10730,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), None{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(10735,5)
            pub fn PropagateFailure<_U: DafnyType>(&self) -> Rc<crate::Std::Wrappers::Option<_U>> {
                Rc::new(crate::Std::Wrappers::Option::None::<_U> {})
            }
            /// DafnyStandardLibraries-rs.dfy(10741,5)
            pub fn Extract(&self) -> T {
                self.value().clone()
            }
            /// DafnyStandardLibraries-rs.dfy(10747,5)
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
            /// DafnyStandardLibraries-rs.dfy(10756,5)
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
            /// DafnyStandardLibraries-rs.dfy(10765,5)
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
            /// DafnyStandardLibraries-rs.dfy(10774,5)
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

        /// DafnyStandardLibraries-rs.dfy(10780,3)
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
            /// DafnyStandardLibraries-rs.dfy(10781,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), Failure{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(10786,5)
            pub fn PropagateFailure<_U: DafnyType>(&self) -> Rc<crate::Std::Wrappers::Result<_U, E>> {
                Rc::new(crate::Std::Wrappers::Result::Failure::<_U, E> {
                        error: self.error().clone()
                    })
            }
            /// DafnyStandardLibraries-rs.dfy(10792,5)
            pub fn Extract(&self) -> R {
                self.value().clone()
            }
            /// DafnyStandardLibraries-rs.dfy(10798,5)
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
            /// DafnyStandardLibraries-rs.dfy(10807,5)
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
            /// DafnyStandardLibraries-rs.dfy(10816,5)
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
            /// DafnyStandardLibraries-rs.dfy(10825,5)
            pub fn Map<_FC: DafnyType>(&self, rewrap: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Wrappers::Result<R, E>>) -> _FC>) -> _FC {
                rewrap(&Rc::new(self.clone()))
            }
            /// DafnyStandardLibraries-rs.dfy(10830,5)
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

        /// DafnyStandardLibraries-rs.dfy(10840,3)
        #[derive(Clone)]
        pub enum Outcome<E: DafnyType> {
            Pass {},
            Fail {
                error: E
            }
        }

        impl<E: DafnyType> Outcome<E> {
            /// DafnyStandardLibraries-rs.dfy(10841,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), Fail{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(10846,5)
            pub fn PropagateFailure(&self) -> Rc<crate::Std::Wrappers::Outcome<E>> {
                Rc::new(self.clone())
            }
            /// DafnyStandardLibraries-rs.dfy(10852,5)
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
            /// DafnyStandardLibraries-rs.dfy(10861,5)
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
            /// DafnyStandardLibraries-rs.dfy(10870,5)
            pub fn Map<_FC: DafnyType>(&self, rewrap: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Wrappers::Outcome<E>>) -> _FC>) -> _FC {
                rewrap(&Rc::new(self.clone()))
            }
            /// DafnyStandardLibraries-rs.dfy(10875,5)
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
            /// DafnyStandardLibraries-rs.dfy(10884,5)
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

        /// DafnyStandardLibraries-rs.dfy(10893,3)
        #[derive(Clone)]
        pub enum OutcomeResult<E: DafnyType> {
            _Pass_k {},
            _Fail_k {
                error: E
            }
        }

        impl<E: DafnyType> OutcomeResult<E> {
            /// DafnyStandardLibraries-rs.dfy(10894,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), _Fail_k{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(10899,5)
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
  crate::SimpleTest::_default::Main(&dafny_args);
}