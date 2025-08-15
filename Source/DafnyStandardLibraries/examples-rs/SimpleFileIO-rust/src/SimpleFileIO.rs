#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
#![cfg_attr(any(), rustfmt::skip)]

pub mod _module {
    
}
/// *****************************************************************************
///  Copyright by the contributors to the Dafny Project
///  SPDX-License-Identifier: MIT
/// *****************************************************************************
/// Source/DafnyStandardLibraries/examples/SimpleFileIO.dfy(7,1)
pub mod SimpleFileIO {
    pub use ::dafny_runtime::Sequence;
    pub use ::dafny_runtime::DafnyChar;
    pub use ::dafny_runtime::string_of;
    pub use ::std::rc::Rc;
    pub use crate::Std::Wrappers::Result;
    pub use crate::Std::Wrappers::Result::Success;
    pub use ::dafny_runtime::DafnyPrintWrapper;

    pub struct _default {}

    impl _default {
        /// Source/DafnyStandardLibraries/examples/SimpleFileIO.dfy(11,3)
        pub fn Main(_noArgsParameter: &Sequence<Sequence<DafnyChar>>) -> () {
            let mut filename: Sequence<DafnyChar> = string_of("Source/DafnyStandardLibraries/examples/SimpleFileIO.dfy");
            let mut readResult: Rc<Result<Sequence<u8>, Sequence<DafnyChar>>>;
            let mut _out0: Rc<Result<Sequence<u8>, Sequence<DafnyChar>>> = crate::Std::FileIO::_default::ReadBytesFromFile(&filename);
            readResult = _out0.clone();
            let mut _source0: Rc<Result<Sequence<u8>, Sequence<DafnyChar>>> = readResult.clone();
            if matches!((&_source0).as_ref(), Success{ .. }) {
                let mut ___mcc_h0: Sequence<u8> = _source0.value().clone();
                let mut content: Sequence<u8> = ___mcc_h0.clone();
                print!("{}", DafnyPrintWrapper(&string_of("Successfully read ")));
                print!("{}", DafnyPrintWrapper(&content.cardinality()));
                print!("{}", DafnyPrintWrapper(&string_of(" bytes from ")));
                print!("{}", DafnyPrintWrapper(&filename));
                print!("{}", DafnyPrintWrapper(&string_of("\n")));
                print!("{}", DafnyPrintWrapper(&string_of("FileIO test: PASSED\n")))
            } else {
                let mut ___mcc_h1: Sequence<DafnyChar> = _source0.error().clone();
                let mut error: Sequence<DafnyChar> = ___mcc_h1.clone();
                print!("{}", DafnyPrintWrapper(&string_of("Failed to read file: ")));
                print!("{}", DafnyPrintWrapper(&error));
                print!("{}", DafnyPrintWrapper(&string_of("\n")));
                print!("{}", DafnyPrintWrapper(&string_of("FileIO test: FAILED\n")))
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

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(6231,3)
                pub fn Get<_X: DafnyTypeEq, _Y: DafnyType>(m: &Map<_X, _Y>, x: &_X) -> Rc<Option<_Y>> {
                    if m.contains(x) {
                        Rc::new(Option::Some::<_Y> {
                                value: m.get(&((x)/*<i>Coercion from _X to ::dafny_runtime::DafnyInt</i> not yet implemented*/))
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

    pub mod JSON {
        /// DafnyStandardLibraries-rs.dfy(8134,1)
        pub mod API {
            pub use ::std::rc::Rc;
            pub use crate::Std::JSON::Values::JSON;
            pub use crate::Std::Wrappers::Result;
            pub use ::dafny_runtime::Sequence;
            pub use crate::Std::JSON::Errors::SerializationError;
            pub use crate::Std::JSON::Grammar::Structural;
            pub use crate::Std::JSON::Grammar::Value;
            pub use ::dafny_runtime::Object;
            pub use ::dafny_runtime::MaybePlacebo;
            pub use crate::Std::JSON::Errors::DeserializationError;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(8135,3)
                pub fn Serialize(js: &Rc<JSON>) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Rc<Structural<Rc<Value>>>, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::JSON(js);
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Sequence<u8>>()
                    } else {
                        let mut js: Rc<Structural<Rc<Value>>> = valueOrError0.Extract();
                        crate::Std::JSON::ZeroCopy::API::_default::Serialize(&js)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8140,3)
                pub fn SerializeAlloc(js: &Rc<JSON>) -> Rc<Result<Object<[u8]>, Rc<SerializationError>>> {
                    let mut bs = MaybePlacebo::<Rc<Result<Object<[u8]>, Rc<SerializationError>>>>::new();
                    let mut valueOrError0: Rc<Result<Rc<Structural<Rc<Value>>>, Rc<SerializationError>>>;
                    valueOrError0 = crate::Std::JSON::Serializer::_default::JSON(js);
                    if valueOrError0.IsFailure() {
                        bs = MaybePlacebo::from(valueOrError0.PropagateFailure::<Object<[u8]>>());
                        return bs.read();
                    };
                    let mut js: Rc<Structural<Rc<Value>>> = valueOrError0.Extract();
                    let mut _out0: Rc<Result<Object<[u8]>, Rc<SerializationError>>>;
                    _out0 = crate::Std::JSON::ZeroCopy::API::_default::SerializeAlloc(&js);
                    bs = MaybePlacebo::from(_out0.clone());
                    return bs.read();
                }
                /// DafnyStandardLibraries-rs.dfy(8146,3)
                pub fn SerializeInto(js: &Rc<JSON>, bs: &Object<[u8]>) -> Rc<Result<u32, Rc<SerializationError>>> {
                    let mut len = MaybePlacebo::<Rc<Result<u32, Rc<SerializationError>>>>::new();
                    let mut valueOrError0: Rc<Result<Rc<Structural<Rc<Value>>>, Rc<SerializationError>>>;
                    valueOrError0 = crate::Std::JSON::Serializer::_default::JSON(js);
                    if valueOrError0.IsFailure() {
                        len = MaybePlacebo::from(valueOrError0.PropagateFailure::<u32>());
                        return len.read();
                    };
                    let mut js: Rc<Structural<Rc<Value>>> = valueOrError0.Extract();
                    let mut _out0: Rc<Result<u32, Rc<SerializationError>>>;
                    _out0 = crate::Std::JSON::ZeroCopy::API::_default::SerializeInto(&js, bs);
                    len = MaybePlacebo::from(_out0.clone());
                    return len.read();
                }
                /// DafnyStandardLibraries-rs.dfy(8153,3)
                pub fn Deserialize(bs: &Sequence<u8>) -> Rc<Result<Rc<JSON>, Rc<DeserializationError>>> {
                    let mut valueOrError0: Rc<Result<Rc<Structural<Rc<Value>>>, Rc<DeserializationError>>> = crate::Std::JSON::ZeroCopy::API::_default::Deserialize(bs);
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Rc<JSON>>()
                    } else {
                        let mut js: Rc<Structural<Rc<Value>>> = valueOrError0.Extract();
                        crate::Std::JSON::Deserializer::_default::JSON(&js)
                    }
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(8171,1)
        pub mod ByteStrConversion {
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::seq;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::itertools::Itertools;
            pub use ::std::rc::Rc;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::euclidian_modulo;
            pub use ::dafny_runtime::euclidian_division;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::std::primitive::char;
            pub use ::dafny_runtime::Map;
            pub use ::dafny_runtime::map;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(13002,5)
                pub fn BASE() -> nat {
                    crate::Std::JSON::ByteStrConversion::_default::base()
                }
                /// DafnyStandardLibraries-rs.dfy(13007,5)
                pub fn IsDigitChar(c: u8) -> bool {
                    crate::Std::JSON::ByteStrConversion::_default::charToDigit().contains(&c)
                }
                /// DafnyStandardLibraries-rs.dfy(13012,5)
                pub fn OfDigits(digits: &Sequence<crate::Std::JSON::ByteStrConversion::digit>) -> Sequence<u8> {
                    let mut _accumulator: Sequence<u8> = seq![] as Sequence<u8>;
                    let mut _r0 = digits.clone();
                    'TAIL_CALL_START: loop {
                        let digits = _r0;
                        if digits.clone().to_array().len() == 0 {
                            return (seq![] as Sequence<u8>).concat(&_accumulator);
                        } else {
                            _accumulator = seq![crate::Std::JSON::ByteStrConversion::_default::chars().get(&digits.get(&int!(0)))].concat(&_accumulator);
                            let mut _in0: Sequence<crate::Std::JSON::ByteStrConversion::digit> = digits.drop(&int!(1));
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13022,5)
                pub fn OfNat(n: &nat) -> Sequence<u8> {
                    if n.clone() == int!(0) {
                        seq![crate::Std::JSON::ByteStrConversion::_default::chars().get(&int!(0))]
                    } else {
                        crate::Std::JSON::ByteStrConversion::_default::OfDigits(&crate::Std::JSON::ByteStrConversion::_default::FromNat(n))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13032,5)
                pub fn IsNumberStr(str: &Sequence<u8>, minus: u8) -> bool {
                    !(!(str.clone().to_array().len() == 0)) || (str.get(&int!(0)) == minus || crate::Std::JSON::ByteStrConversion::_default::charToDigit().contains(&str.get(&int!(0)))) && Itertools::unique((&str.drop(&int!(1))).iter()).all(({
                            let mut str = str.clone();
                            Rc::new(move |__forall_var_0: u8| -> bool{
            let mut c: u8 = __forall_var_0;
            !str.drop(&int!(1)).contains(&c) || crate::Std::JSON::ByteStrConversion::_default::IsDigitChar(c)
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                        }).as_ref())
                }
                /// DafnyStandardLibraries-rs.dfy(13040,5)
                pub fn OfInt(n: &DafnyInt, minus: u8) -> Sequence<u8> {
                    if !(n.clone() < int!(0)) {
                        crate::Std::JSON::ByteStrConversion::_default::OfNat(n)
                    } else {
                        seq![minus].concat(&crate::Std::JSON::ByteStrConversion::_default::OfNat(&(int!(0) - n.clone())))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13050,5)
                pub fn ToNat(str: &Sequence<u8>) -> nat {
                    if str.clone().to_array().len() == 0 {
                        int!(0)
                    } else {
                        let mut c: u8 = str.get(&(str.cardinality() - int!(1)));
                        crate::Std::JSON::ByteStrConversion::_default::ToNat(&str.take(&(str.cardinality() - int!(1)))) * crate::Std::JSON::ByteStrConversion::_default::base() + crate::Std::JSON::ByteStrConversion::_default::charToDigit().get(&c)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13090,5)
                pub fn ToInt(str: &Sequence<u8>, minus: u8) -> DafnyInt {
                    if seq![minus] <= str.clone() {
                        int!(0) - crate::Std::JSON::ByteStrConversion::_default::ToNat(&str.drop(&int!(1)))
                    } else {
                        crate::Std::JSON::ByteStrConversion::_default::ToNat(str)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(2728,3)
                pub fn ToNatRight(xs: &Sequence<crate::Std::JSON::ByteStrConversion::digit>) -> nat {
                    if xs.cardinality() == int!(0) {
                        int!(0)
                    } else {
                        crate::Std::JSON::ByteStrConversion::_default::ToNatRight(&crate::Std::Collections::Seq::_default::DropFirst::<crate::Std::JSON::ByteStrConversion::digit>(xs)) * crate::Std::JSON::ByteStrConversion::_default::BASE() + crate::Std::Collections::Seq::_default::First::<crate::Std::JSON::ByteStrConversion::digit>(xs)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(2736,3)
                pub fn ToNatLeft(xs: &Sequence<crate::Std::JSON::ByteStrConversion::digit>) -> nat {
                    let mut _accumulator: nat = int!(0);
                    let mut _r0 = xs.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        if xs.cardinality() == int!(0) {
                            return int!(0) + _accumulator.clone();
                        } else {
                            _accumulator = crate::Std::Collections::Seq::_default::Last::<DafnyInt>(&xs) * crate::Std::Arithmetic::Power::_default::Pow(&crate::Std::JSON::ByteStrConversion::_default::BASE(), &(xs.cardinality() - int!(1))) + _accumulator.clone();
                            let mut _in0: Sequence<crate::Std::JSON::ByteStrConversion::digit> = crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::ByteStrConversion::digit>(&xs);
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3020,3)
                pub fn FromNat(n: &nat) -> Sequence<crate::Std::JSON::ByteStrConversion::digit> {
                    let mut _accumulator: Sequence<crate::Std::JSON::ByteStrConversion::digit> = seq![] as Sequence<crate::Std::JSON::ByteStrConversion::digit>;
                    let mut _r0 = n.clone();
                    'TAIL_CALL_START: loop {
                        let n = _r0;
                        if n.clone() == int!(0) {
                            return _accumulator.concat(&(seq![] as Sequence<DafnyInt>));
                        } else {
                            _accumulator = _accumulator.concat(&seq![euclidian_modulo(n.clone(), crate::Std::JSON::ByteStrConversion::_default::BASE())]);
                            let mut _in0: DafnyInt = euclidian_division(n.clone(), crate::Std::JSON::ByteStrConversion::_default::BASE());
                            _r0 = _in0.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3104,3)
                pub fn SeqExtend(xs: &Sequence<crate::Std::JSON::ByteStrConversion::digit>, n: &nat) -> Sequence<crate::Std::JSON::ByteStrConversion::digit> {
                    let mut _r0 = xs.clone();
                    let mut _r1 = n.clone();
                    'TAIL_CALL_START: loop {
                        let xs = _r0;
                        let n = _r1;
                        if !(xs.cardinality() < n.clone()) {
                            return xs.clone();
                        } else {
                            let mut _in0: Sequence<crate::Std::JSON::ByteStrConversion::digit> = xs.concat(&seq![int!(0)]);
                            let mut _in1: nat = n.clone();
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(3116,3)
                pub fn SeqExtendMultiple(xs: &Sequence<crate::Std::JSON::ByteStrConversion::digit>, n: &nat) -> Sequence<crate::Std::JSON::ByteStrConversion::digit> {
                    let mut newLen: DafnyInt = xs.cardinality() + n.clone() - euclidian_modulo(xs.cardinality(), n.clone());
                    crate::Std::JSON::ByteStrConversion::_default::SeqExtend(xs, &newLen)
                }
                /// DafnyStandardLibraries-rs.dfy(3130,3)
                pub fn FromNatWithLen(n: &nat, len: &nat) -> Sequence<crate::Std::JSON::ByteStrConversion::digit> {
                    crate::Std::JSON::ByteStrConversion::_default::SeqExtend(&crate::Std::JSON::ByteStrConversion::_default::FromNat(n), len)
                }
                /// DafnyStandardLibraries-rs.dfy(3153,3)
                pub fn SeqZero(len: &nat) -> Sequence<crate::Std::JSON::ByteStrConversion::digit> {
                    let mut xs: Sequence<crate::Std::JSON::ByteStrConversion::digit> = crate::Std::JSON::ByteStrConversion::_default::FromNatWithLen(&int!(0), len);
                    xs.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(3182,3)
                pub fn SeqAdd(xs: &Sequence<crate::Std::JSON::ByteStrConversion::digit>, ys: &Sequence<crate::Std::JSON::ByteStrConversion::digit>) -> (Sequence<crate::Std::JSON::ByteStrConversion::digit>, nat) {
                    if xs.cardinality() == int!(0) {
                        (
                            seq![] as Sequence<DafnyInt>,
                            int!(0)
                        )
                    } else {
                        let mut __let_tmp_rhs0: (Sequence<crate::Std::JSON::ByteStrConversion::digit>, nat) = crate::Std::JSON::ByteStrConversion::_default::SeqAdd(&crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::ByteStrConversion::digit>(xs), &crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::ByteStrConversion::digit>(ys));
                        let mut _zs_k: Sequence<crate::Std::JSON::ByteStrConversion::digit> = __let_tmp_rhs0.0.clone();
                        let mut cin: nat = __let_tmp_rhs0.1.clone();
                        let mut sum: DafnyInt = crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) + crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) + cin.clone();
                        let mut __let_tmp_rhs1: (DafnyInt, DafnyInt) = if sum.clone() < crate::Std::JSON::ByteStrConversion::_default::BASE() {
                                (
                                    sum.clone(),
                                    int!(0)
                                )
                            } else {
                                (
                                    sum.clone() - crate::Std::JSON::ByteStrConversion::_default::BASE(),
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
                pub fn SeqSub(xs: &Sequence<crate::Std::JSON::ByteStrConversion::digit>, ys: &Sequence<crate::Std::JSON::ByteStrConversion::digit>) -> (Sequence<crate::Std::JSON::ByteStrConversion::digit>, nat) {
                    if xs.cardinality() == int!(0) {
                        (
                            seq![] as Sequence<DafnyInt>,
                            int!(0)
                        )
                    } else {
                        let mut __let_tmp_rhs0: (Sequence<crate::Std::JSON::ByteStrConversion::digit>, nat) = crate::Std::JSON::ByteStrConversion::_default::SeqSub(&crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::ByteStrConversion::digit>(xs), &crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::ByteStrConversion::digit>(ys));
                        let mut zs: Sequence<crate::Std::JSON::ByteStrConversion::digit> = __let_tmp_rhs0.0.clone();
                        let mut cin: nat = __let_tmp_rhs0.1.clone();
                        let mut __let_tmp_rhs1: (DafnyInt, DafnyInt) = if !(crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) < crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) + cin.clone()) {
                                (
                                    crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) - crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) - cin.clone(),
                                    int!(0)
                                )
                            } else {
                                (
                                    crate::Std::JSON::ByteStrConversion::_default::BASE() + crate::Std::Collections::Seq::_default::Last::<crate::Std::JSON::ByteStrConversion::digit>(xs) - crate::Std::Collections::Seq::_default::Last::<crate::Std::JSON::ByteStrConversion::digit>(ys) - cin.clone(),
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
                /// DafnyStandardLibraries-rs.dfy(8173,3)
                pub fn chars() -> crate::Std::JSON::ByteStrConversion::CharSeq {
                    seq![DafnyChar(char::from_u32(48).unwrap()).0 as u8, DafnyChar(char::from_u32(49).unwrap()).0 as u8, DafnyChar(char::from_u32(50).unwrap()).0 as u8, DafnyChar(char::from_u32(51).unwrap()).0 as u8, DafnyChar(char::from_u32(52).unwrap()).0 as u8, DafnyChar(char::from_u32(53).unwrap()).0 as u8, DafnyChar(char::from_u32(54).unwrap()).0 as u8, DafnyChar(char::from_u32(55).unwrap()).0 as u8, DafnyChar(char::from_u32(56).unwrap()).0 as u8, DafnyChar(char::from_u32(57).unwrap()).0 as u8]
                }
                /// DafnyStandardLibraries-rs.dfy(12996,5)
                pub fn base() -> DafnyInt {
                    crate::Std::JSON::ByteStrConversion::_default::chars().cardinality()
                }
                /// DafnyStandardLibraries-rs.dfy(8174,3)
                pub fn charToDigit() -> Map<u8, crate::Std::JSON::ByteStrConversion::digit> {
                    map![DafnyChar(char::from_u32(48).unwrap()).0 as u8 => int!(0), DafnyChar(char::from_u32(49).unwrap()).0 as u8 => int!(1), DafnyChar(char::from_u32(50).unwrap()).0 as u8 => int!(2), DafnyChar(char::from_u32(51).unwrap()).0 as u8 => int!(3), DafnyChar(char::from_u32(52).unwrap()).0 as u8 => int!(4), DafnyChar(char::from_u32(53).unwrap()).0 as u8 => int!(5), DafnyChar(char::from_u32(54).unwrap()).0 as u8 => int!(6), DafnyChar(char::from_u32(55).unwrap()).0 as u8 => int!(7), DafnyChar(char::from_u32(56).unwrap()).0 as u8 => int!(8), DafnyChar(char::from_u32(57).unwrap()).0 as u8 => int!(9)]
                }
            }

            /// DafnyStandardLibraries-rs.dfy(13106,5)
            pub type CharSeq = Sequence<u8>;

            /// DafnyStandardLibraries-rs.dfy(3285,3)
            pub type digit = DafnyInt;
        }

        pub mod ConcreteSyntax {
            /// DafnyStandardLibraries-rs.dfy(8186,1)
            pub mod Spec {
                pub use crate::Std::JSON::Utils::Views::Core::View;
                pub use ::dafny_runtime::Sequence;
                pub use crate::Std::JSON::Utils::Views::Core::View_;
                pub use ::std::convert::AsRef;
                pub use ::dafny_runtime::DafnyType;
                pub use ::std::rc::Rc;
                pub use crate::Std::JSON::Grammar::Structural;
                pub use crate::Std::JSON::Grammar::Maybe;
                pub use crate::Std::JSON::Grammar::Maybe::Empty;
                pub use ::dafny_runtime::seq;
                pub use ::dafny_runtime::int;
                pub use crate::Std::JSON::Grammar::Bracketed;
                pub use crate::Std::JSON::Grammar::Suffixed;
                pub use crate::Std::JSON::Grammar::jKeyValue;
                pub use crate::Std::JSON::Grammar::jfrac;
                pub use crate::Std::JSON::Grammar::jexp;
                pub use crate::Std::JSON::Grammar::jnumber;
                pub use crate::Std::JSON::Grammar::jstring;
                pub use crate::Std::JSON::Grammar::jcomma;
                pub use crate::Std::JSON::Grammar::Value;
                pub use crate::Std::JSON::Grammar::jlbrace;
                pub use crate::Std::JSON::Grammar::jrbrace;
                pub use crate::Std::JSON::Grammar::jlbracket;
                pub use crate::Std::JSON::Grammar::jrbracket;
                pub use crate::Std::JSON::Grammar::Value::Null;
                pub use crate::Std::JSON::Grammar::jnull;
                pub use crate::Std::JSON::Grammar::Value::Bool;
                pub use crate::Std::JSON::Grammar::jbool;
                pub use crate::Std::JSON::Grammar::Value::String;
                pub use crate::Std::JSON::Grammar::Value::Number;
                pub use crate::Std::JSON::Grammar::Value::Object;

                pub struct _default {}

                impl _default {
                    /// DafnyStandardLibraries-rs.dfy(8187,3)
                    pub fn View(v: &View) -> Sequence<u8> {
                        View_::Bytes(AsRef::as_ref(v))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8192,3)
                    pub fn Structural<_T: DafnyType>(_self: &Rc<Structural<_T>>, fT: &Rc<dyn ::std::ops::Fn(&_T) -> Sequence<u8>>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.before()).concat(&fT(_self.t())).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.after()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8197,3)
                    pub fn StructuralView(_self: &Rc<Structural<View>>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::Structural::<View>(_self, &(Rc::new(move |x0: &View| crate::Std::JSON::ConcreteSyntax::Spec::_default::View(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8202,3)
                    pub fn Maybe<_T: DafnyType>(_self: &Rc<Maybe<_T>>, fT: &Rc<dyn ::std::ops::Fn(&_T) -> Sequence<u8>>) -> Sequence<u8> {
                        if matches!(_self.as_ref(), Empty{ .. }) {
                            seq![] as Sequence<u8>
                        } else {
                            fT(_self.t())
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(8212,3)
                    pub fn ConcatBytes<_T: DafnyType>(ts: &Sequence<_T>, fT: &Rc<dyn ::std::ops::Fn(&_T) -> Sequence<u8>>) -> Sequence<u8> {
                        let mut _accumulator: Sequence<u8> = seq![] as Sequence<u8>;
                        let mut _r0 = ts.clone();
                        let mut _r1 = fT.clone();
                        'TAIL_CALL_START: loop {
                            let ts = _r0;
                            let fT = _r1;
                            if ts.cardinality() == int!(0) {
                                return _accumulator.concat(&(seq![] as Sequence<u8>));
                            } else {
                                _accumulator = _accumulator.concat(&(&fT)(&ts.get(&int!(0))));
                                let mut _in0: Sequence<_T> = ts.drop(&int!(1));
                                let mut _in1: Rc<dyn ::std::ops::Fn(&_T) -> Sequence<u8>> = fT.clone();
                                _r0 = _in0.clone();
                                _r1 = _in1.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(8222,3)
                    pub fn Bracketed<_D: DafnyType, _S: DafnyType>(_self: &Rc<Bracketed<View, _D, _S, View>>, fDatum: &Rc<dyn ::std::ops::Fn(&Rc<Suffixed<_D, _S>>) -> Sequence<u8>>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::StructuralView(_self.l()).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::ConcatBytes::<Rc<Suffixed<_D, _S>>>(_self.data(), fDatum)).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::StructuralView(_self.r()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8228,3)
                    pub fn KeyValue(_self: &Rc<jKeyValue>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::String(_self.k()).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::StructuralView(_self.colon())).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::Value(_self.v()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8233,3)
                    pub fn Frac(_self: &Rc<jfrac>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.period()).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.num()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8238,3)
                    pub fn Exp(_self: &Rc<jexp>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.e()).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.sign())).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.num()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8243,3)
                    pub fn Number(_self: &Rc<jnumber>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.minus()).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.num())).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::Maybe::<Rc<jfrac>>(_self.frac(), &(Rc::new(move |x0: &Rc<jfrac>| crate::Std::JSON::ConcreteSyntax::Spec::_default::Frac(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>))).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::Maybe::<Rc<jexp>>(_self.exp(), &(Rc::new(move |x0: &Rc<jexp>| crate::Std::JSON::ConcreteSyntax::Spec::_default::Exp(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>)))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8248,3)
                    pub fn String(_self: &Rc<jstring>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.lq()).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.contents())).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::View(_self.rq()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8253,3)
                    pub fn CommaSuffix(c: &Rc<Maybe<Rc<Structural<jcomma>>>>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::Maybe::<Rc<Structural<View>>>(c, &(Rc::new(move |x0: &Rc<Structural<View>>| crate::Std::JSON::ConcreteSyntax::Spec::_default::StructuralView(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8258,3)
                    pub fn Member(_self: &Rc<Suffixed<Rc<jKeyValue>, jcomma>>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::KeyValue(_self.t()).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::CommaSuffix(_self.suffix()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8263,3)
                    pub fn Item(_self: &Rc<Suffixed<Rc<Value>, jcomma>>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::Value(_self.t()).concat(&crate::Std::JSON::ConcreteSyntax::Spec::_default::CommaSuffix(_self.suffix()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(8268,3)
                    pub fn Object(obj: &Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::Bracketed::<Rc<jKeyValue>, jcomma>(obj, {
                                let obj: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = obj.clone();
                                &({
                                    Rc::new(move |d: &Rc<Suffixed<Rc<jKeyValue>, jcomma>>| -> Sequence<u8>{
            crate::Std::JSON::ConcreteSyntax::Spec::_default::Member(d)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                })
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(8273,3)
                    pub fn Array(arr: &Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::Bracketed::<Rc<Value>, jcomma>(arr, {
                                let arr: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = arr.clone();
                                &({
                                    Rc::new(move |d: &Rc<Suffixed<Rc<Value>, jcomma>>| -> Sequence<u8>{
            crate::Std::JSON::ConcreteSyntax::Spec::_default::Item(d)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                })
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(8278,3)
                    pub fn Value(_self: &Rc<Value>) -> Sequence<u8> {
                        let mut _source0: Rc<Value> = _self.clone();
                        if matches!((&_source0).as_ref(), Null{ .. }) {
                            let mut ___mcc_h0: jnull = _source0.n().clone();
                            let mut n: jnull = ___mcc_h0.clone();
                            crate::Std::JSON::ConcreteSyntax::Spec::_default::View(&n)
                        } else {
                            if matches!((&_source0).as_ref(), Bool{ .. }) {
                                let mut ___mcc_h1: jbool = _source0.b().clone();
                                let mut b: jbool = ___mcc_h1.clone();
                                crate::Std::JSON::ConcreteSyntax::Spec::_default::View(&b)
                            } else {
                                if matches!((&_source0).as_ref(), String{ .. }) {
                                    let mut ___mcc_h2: Rc<jstring> = _source0.str().clone();
                                    let mut str: Rc<jstring> = ___mcc_h2.clone();
                                    crate::Std::JSON::ConcreteSyntax::Spec::_default::String(&str)
                                } else {
                                    if matches!((&_source0).as_ref(), Number{ .. }) {
                                        let mut ___mcc_h3: Rc<jnumber> = _source0.num().clone();
                                        let mut num: Rc<jnumber> = ___mcc_h3.clone();
                                        crate::Std::JSON::ConcreteSyntax::Spec::_default::Number(&num)
                                    } else {
                                        if matches!((&_source0).as_ref(), Object{ .. }) {
                                            let mut ___mcc_h4: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = _source0.obj().clone();
                                            let mut obj: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = ___mcc_h4.clone();
                                            crate::Std::JSON::ConcreteSyntax::Spec::_default::Object(&obj)
                                        } else {
                                            let mut ___mcc_h5: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = _source0.arr().clone();
                                            let mut arr: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = ___mcc_h5.clone();
                                            crate::Std::JSON::ConcreteSyntax::Spec::_default::Array(&arr)
                                        }
                                    }
                                }
                            }
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(8321,3)
                    pub fn JSON(js: &Rc<Structural<Rc<Value>>>) -> Sequence<u8> {
                        crate::Std::JSON::ConcreteSyntax::Spec::_default::Structural::<Rc<Value>>(js, &(Rc::new(move |x0: &Rc<Value>| crate::Std::JSON::ConcreteSyntax::Spec::_default::Value(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>))
                    }
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8333,1)
            pub mod SpecProperties {
                
            }
        }

        /// DafnyStandardLibraries-rs.dfy(8386,1)
        pub mod Deserializer {
            pub use crate::Std::JSON::Grammar::jbool;
            pub use crate::Std::JSON::Utils::Views::Core::View_;
            pub use ::std::convert::AsRef;
            pub use ::dafny_runtime::truncate;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::std::primitive::char;
            pub use ::dafny_runtime::Sequence;
            pub use ::std::rc::Rc;
            pub use crate::Std::JSON::Errors::DeserializationError;
            pub use ::dafny_runtime::string_of;
            pub use ::dafny_runtime::_System::nat;
            pub use crate::Std::Wrappers::Result;
            pub use ::dafny_runtime::itertools::Itertools;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::seq;
            pub use crate::Std::JSON::Grammar::jstring;
            pub use crate::Std::JSON::Grammar::jsign;
            pub use crate::Std::JSON::Grammar::jnum;
            pub use crate::Std::JSON::Grammar::jnumber;
            pub use crate::Std::JSON::Values::Decimal;
            pub use crate::Std::JSON::Grammar::jminus;
            pub use crate::Std::JSON::Grammar::Maybe;
            pub use crate::Std::JSON::Grammar::jfrac;
            pub use crate::Std::JSON::Grammar::jexp;
            pub use crate::Std::JSON::Grammar::Maybe::Empty;
            pub use crate::Std::JSON::Grammar::je;
            pub use crate::Std::JSON::Grammar::jperiod;
            pub use crate::Std::JSON::Grammar::jKeyValue;
            pub use crate::Std::JSON::Values::JSON;
            pub use crate::Std::JSON::Grammar::Bracketed;
            pub use crate::Std::JSON::Grammar::jlbrace;
            pub use crate::Std::JSON::Grammar::jcomma;
            pub use crate::Std::JSON::Grammar::jrbrace;
            pub use crate::Std::JSON::Grammar::Suffixed;
            pub use crate::Std::JSON::Grammar::jlbracket;
            pub use crate::Std::JSON::Grammar::Value;
            pub use crate::Std::JSON::Grammar::jrbracket;
            pub use crate::Std::JSON::Grammar::Value::Null;
            pub use crate::Std::JSON::Grammar::jnull;
            pub use crate::Std::JSON::Grammar::Value::Bool;
            pub use crate::Std::JSON::Grammar::Value::String;
            pub use crate::Std::JSON::Grammar::Value::Number;
            pub use crate::Std::JSON::Grammar::Value::Object;
            pub use crate::Std::JSON::Grammar::Structural;
            pub use ::dafny_runtime::Map;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(8387,3)
                pub fn Bool(js: &jbool) -> bool {
                    View_::At(AsRef::as_ref(js), truncate!(int!(0), u32)) == DafnyChar(char::from_u32(116).unwrap()).0 as u8
                }
                /// DafnyStandardLibraries-rs.dfy(8393,3)
                pub fn UnsupportedEscape16(code: &Sequence<u16>) -> Rc<DeserializationError> {
                    Rc::new(DeserializationError::UnsupportedEscape {
                            str: crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::FromUTF16Checked(code).ToOption().GetOr(&string_of("Couldn't decode UTF-16"))
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8400,3)
                pub fn ToNat16(str: &Sequence<u16>) -> u16 {
                    let mut hd: nat = crate::Std::JSON::Deserializer::Uint16StrConversion::_default::ToNat(str);
                    truncate!(hd.clone(), u16)
                }
                /// DafnyStandardLibraries-rs.dfy(8411,3)
                pub fn Unescape(str: &Sequence<u16>, start: &nat, prefix: &Sequence<u16>) -> Rc<Result<Sequence<u16>, Rc<DeserializationError>>> {
                    let mut _r0 = str.clone();
                    let mut _r1 = start.clone();
                    let mut _r2 = prefix.clone();
                    'TAIL_CALL_START: loop {
                        let str = _r0;
                        let start = _r1;
                        let prefix = _r2;
                        if !(start.clone() < str.cardinality()) {
                            return Rc::new(Result::Success::<Sequence<u16>, Rc<DeserializationError>> {
                                        value: prefix.clone()
                                    });
                        } else {
                            if str.get(&start) == DafnyChar(char::from_u32(92).unwrap()).0 as u16 {
                                if str.cardinality() == start.clone() + int!(1) {
                                    return Rc::new(Result::Failure::<Sequence<u16>, Rc<DeserializationError>> {
                                                error: Rc::new(DeserializationError::EscapeAtEOS {})
                                            });
                                } else {
                                    let mut c: u16 = str.get(&(start.clone() + int!(1)));
                                    if c == DafnyChar(char::from_u32(117).unwrap()).0 as u16 {
                                        if str.cardinality() < start.clone() + int!(6) {
                                            return Rc::new(Result::Failure::<Sequence<u16>, Rc<DeserializationError>> {
                                                        error: Rc::new(DeserializationError::EscapeAtEOS {})
                                                    });
                                        } else {
                                            let mut code: Sequence<u16> = str.slice(&(start.clone() + int!(2)), &(start.clone() + int!(6)));
                                            if Itertools::unique((&code).iter()).any(({
                                                        let mut code = code.clone();
                                                        Rc::new(move |__exists_var_0: u16| -> bool{
            let mut c: u16 = __exists_var_0;
            code.contains(&c) && !crate::Std::JSON::Deserializer::_default::HEX_TABLE_16().contains(&c)
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                                                    }).as_ref()) {
                                                return Rc::new(Result::Failure::<Sequence<u16>, Rc<DeserializationError>> {
                                                            error: crate::Std::JSON::Deserializer::_default::UnsupportedEscape16(&code)
                                                        });
                                            } else {
                                                let mut hd: u16 = crate::Std::JSON::Deserializer::_default::ToNat16(&code);
                                                let mut _in0: Sequence<u16> = str.clone();
                                                let mut _in1: DafnyInt = start.clone() + int!(6);
                                                let mut _in2: Sequence<u16> = prefix.concat(&seq![hd]);
                                                _r0 = _in0.clone();
                                                _r1 = _in1.clone();
                                                _r2 = _in2.clone();
                                                continue 'TAIL_CALL_START;
                                            }
                                        }
                                    } else {
                                        let mut unescaped: u16 = if c == truncate!(int!(34), u16) {
                                                truncate!(int!(34), u16)
                                            } else {
                                                if c == truncate!(int!(92), u16) {
                                                    truncate!(int!(92), u16)
                                                } else {
                                                    if c == truncate!(int!(98), u16) {
                                                        truncate!(int!(8), u16)
                                                    } else {
                                                        if c == truncate!(int!(102), u16) {
                                                            truncate!(int!(12), u16)
                                                        } else {
                                                            if c == truncate!(int!(110), u16) {
                                                                truncate!(int!(10), u16)
                                                            } else {
                                                                if c == truncate!(int!(114), u16) {
                                                                    truncate!(int!(13), u16)
                                                                } else {
                                                                    if c == truncate!(int!(116), u16) {
                                                                        truncate!(int!(9), u16)
                                                                    } else {
                                                                        truncate!(int!(0), u16)
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            };
                                        if int!(unescaped) == int!(0) {
                                            return Rc::new(Result::Failure::<Sequence<u16>, Rc<DeserializationError>> {
                                                        error: crate::Std::JSON::Deserializer::_default::UnsupportedEscape16(&str.slice(&start, &(start.clone() + int!(2))))
                                                    });
                                        } else {
                                            let mut _in3: Sequence<u16> = str.clone();
                                            let mut _in4: DafnyInt = start.clone() + int!(2);
                                            let mut _in5: Sequence<u16> = prefix.concat(&seq![unescaped]);
                                            _r0 = _in3.clone();
                                            _r1 = _in4.clone();
                                            _r2 = _in5.clone();
                                            continue 'TAIL_CALL_START;
                                        }
                                    }
                                }
                            } else {
                                let mut _in6: Sequence<u16> = str.clone();
                                let mut _in7: DafnyInt = start.clone() + int!(1);
                                let mut _in8: Sequence<u16> = prefix.concat(&seq![str.get(&start)]);
                                _r0 = _in6.clone();
                                _r1 = _in7.clone();
                                _r2 = _in8.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8425,3)
                pub fn String(js: &Rc<jstring>) -> Rc<Result<Sequence<DafnyChar>, Rc<DeserializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<DafnyChar>, Rc<DeserializationError>>> = crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::FromUTF8Checked(&View_::Bytes(AsRef::as_ref(js.contents()))).MapFailure::<Rc<DeserializationError>>(&({
                                Rc::new(move |error: &Sequence<DafnyChar>| -> Rc<DeserializationError>{
            Rc::new(DeserializationError::InvalidUnicode {
                    str: error.clone()
                })
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }));
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Sequence<DafnyChar>>()
                    } else {
                        let mut asUtf32: Sequence<DafnyChar> = valueOrError0.Extract();
                        let mut valueOrError1: Rc<Result<Sequence<u16>, Rc<DeserializationError>>> = crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ToUTF16Checked(&asUtf32).ToResult::<Rc<DeserializationError>>(&Rc::new(DeserializationError::InvalidUnicode {
                                        str: string_of("")
                                    }));
                        if valueOrError1.IsFailure() {
                            valueOrError1.PropagateFailure::<Sequence<DafnyChar>>()
                        } else {
                            let mut asUint16: Sequence<u16> = valueOrError1.Extract();
                            let mut valueOrError2: Rc<Result<Sequence<u16>, Rc<DeserializationError>>> = crate::Std::JSON::Deserializer::_default::Unescape(&asUint16, &int!(0), &(seq![] as Sequence<u16>));
                            if valueOrError2.IsFailure() {
                                valueOrError2.PropagateFailure::<Sequence<DafnyChar>>()
                            } else {
                                let mut unescaped: Sequence<u16> = valueOrError2.Extract();
                                crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::FromUTF16Checked(&unescaped).MapFailure::<Rc<DeserializationError>>(&({
                                        Rc::new(move |error: &Sequence<DafnyChar>| -> Rc<DeserializationError>{
            Rc::new(DeserializationError::InvalidUnicode {
                    str: error.clone()
                })
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                    }))
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8433,3)
                pub fn ToInt(sign: &jsign, n: &jnum) -> Rc<Result<DafnyInt, Rc<DeserializationError>>> {
                    let mut n: DafnyInt = crate::Std::JSON::ByteStrConversion::_default::ToNat(&View_::Bytes(AsRef::as_ref(n)));
                    Rc::new(Result::Success::<DafnyInt, Rc<DeserializationError>> {
                            value: if View_::_Char_q(AsRef::as_ref(sign), &DafnyChar(char::from_u32(45).unwrap())) {
                                    int!(0) - n.clone()
                                } else {
                                    n.clone()
                                }
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8439,3)
                pub fn Number(js: &Rc<jnumber>) -> Rc<Result<Rc<Decimal>, Rc<DeserializationError>>> {
                    let mut __let_tmp_rhs0: Rc<jnumber> = js.clone();
                    let mut minus: jminus = __let_tmp_rhs0.minus().clone();
                    let mut num: jnum = __let_tmp_rhs0.num().clone();
                    let mut frac: Rc<Maybe<Rc<jfrac>>> = __let_tmp_rhs0.frac().clone();
                    let mut exp: Rc<Maybe<Rc<jexp>>> = __let_tmp_rhs0.exp().clone();
                    let mut valueOrError0: Rc<Result<DafnyInt, Rc<DeserializationError>>> = crate::Std::JSON::Deserializer::_default::ToInt(&minus, &num);
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Rc<Decimal>>()
                    } else {
                        let mut n: DafnyInt = valueOrError0.Extract();
                        let mut valueOrError1: Rc<Result<DafnyInt, Rc<DeserializationError>>> = (&({
                                Rc::new(move |_source0: &Rc<Maybe<Rc<jexp>>>| -> Rc<Result<DafnyInt, Rc<DeserializationError>>>{
            if matches!(_source0.as_ref(), Empty{ .. }) {
                Rc::new(Result::Success::<DafnyInt, Rc<DeserializationError>> {
                        value: int!(0)
                    })
            } else {
                let mut ___mcc_h0: Rc<jexp> = _source0.t().clone();
                let mut _source1: Rc<jexp> = ___mcc_h0.clone();
                let mut ___mcc_h1: je = _source1.e().clone();
                let mut ___mcc_h2: jsign = _source1.sign().clone();
                let mut ___mcc_h3: jnum = _source1.num().clone();
                let mut num: jnum = ___mcc_h3.clone();
                let mut sign: jsign = ___mcc_h2.clone();
                crate::Std::JSON::Deserializer::_default::ToInt(&sign, &num)
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }))(&exp);
                        if valueOrError1.IsFailure() {
                            valueOrError1.PropagateFailure::<Rc<Decimal>>()
                        } else {
                            let mut e10: DafnyInt = valueOrError1.Extract();
                            let mut _source2: Rc<Maybe<Rc<jfrac>>> = frac.clone();
                            if matches!((&_source2).as_ref(), Empty{ .. }) {
                                Rc::new(Result::Success::<Rc<Decimal>, Rc<DeserializationError>> {
                                        value: Rc::new(Decimal::Decimal {
                                                    n: n.clone(),
                                                    e10: e10.clone()
                                                })
                                    })
                            } else {
                                let mut ___mcc_h4: Rc<jfrac> = _source2.t().clone();
                                let mut _source3: Rc<jfrac> = ___mcc_h4.clone();
                                let mut ___mcc_h5: jperiod = _source3.period().clone();
                                let mut ___mcc_h6: jnum = _source3.num().clone();
                                let mut num: jnum = ___mcc_h6.clone();
                                let mut pow10: DafnyInt = int!(View_::Length(AsRef::as_ref(&num)));
                                let mut valueOrError2: Rc<Result<DafnyInt, Rc<DeserializationError>>> = crate::Std::JSON::Deserializer::_default::ToInt(&minus, &num);
                                if valueOrError2.IsFailure() {
                                    valueOrError2.PropagateFailure::<Rc<Decimal>>()
                                } else {
                                    let mut frac: DafnyInt = valueOrError2.Extract();
                                    Rc::new(Result::Success::<Rc<Decimal>, Rc<DeserializationError>> {
                                            value: Rc::new(Decimal::Decimal {
                                                        n: n.clone() * crate::Std::Arithmetic::Power::_default::Pow(&int!(10), &pow10) + frac.clone(),
                                                        e10: e10.clone() - pow10.clone()
                                                    })
                                        })
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8445,3)
                pub fn KeyValue(js: &Rc<jKeyValue>) -> Rc<Result<(Sequence<DafnyChar>, Rc<JSON>), Rc<DeserializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<DafnyChar>, Rc<DeserializationError>>> = crate::Std::JSON::Deserializer::_default::String(js.k());
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<(Sequence<DafnyChar>, Rc<JSON>)>()
                    } else {
                        let mut k: Sequence<DafnyChar> = valueOrError0.Extract();
                        let mut valueOrError1: Rc<Result<Rc<JSON>, Rc<DeserializationError>>> = crate::Std::JSON::Deserializer::_default::Value(js.v());
                        if valueOrError1.IsFailure() {
                            valueOrError1.PropagateFailure::<(Sequence<DafnyChar>, Rc<JSON>)>()
                        } else {
                            let mut v: Rc<JSON> = valueOrError1.Extract();
                            Rc::new(Result::Success::<(Sequence<DafnyChar>, Rc<JSON>), Rc<DeserializationError>> {
                                    value: (
                                            k.clone(),
                                            v.clone()
                                        )
                                })
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8450,3)
                pub fn Object(js: &Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>) -> Rc<Result<Sequence<(Sequence<DafnyChar>, Rc<JSON>)>, Rc<DeserializationError>>> {
                    let mut f: Rc<dyn ::std::ops::Fn(&Rc<Suffixed<Rc<jKeyValue>, jcomma>>) -> Rc<Result<(Sequence<DafnyChar>, Rc<JSON>), Rc<DeserializationError>>>> = {
                            let js: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = js.clone();
                            {
                                Rc::new(move |d: &Rc<Suffixed<Rc<jKeyValue>, jcomma>>| -> Rc<Result<(Sequence<DafnyChar>, Rc<JSON>), Rc<DeserializationError>>>{
            crate::Std::JSON::Deserializer::_default::KeyValue(d.t())
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        };
                    crate::Std::Collections::Seq::_default::MapWithResult::<Rc<Suffixed<Rc<jKeyValue>, jcomma>>, (Sequence<DafnyChar>, Rc<JSON>), Rc<DeserializationError>>(&f, js.data())
                }
                /// DafnyStandardLibraries-rs.dfy(8457,3)
                pub fn Array(js: &Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>) -> Rc<Result<Sequence<Rc<JSON>>, Rc<DeserializationError>>> {
                    let mut f: Rc<dyn ::std::ops::Fn(&Rc<Suffixed<Rc<Value>, jcomma>>) -> Rc<Result<Rc<JSON>, Rc<DeserializationError>>>> = {
                            let js: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = js.clone();
                            {
                                Rc::new(move |d: &Rc<Suffixed<Rc<Value>, jcomma>>| -> Rc<Result<Rc<JSON>, Rc<DeserializationError>>>{
            crate::Std::JSON::Deserializer::_default::Value(d.t())
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        };
                    crate::Std::Collections::Seq::_default::MapWithResult::<Rc<Suffixed<Rc<Value>, jcomma>>, Rc<JSON>, Rc<DeserializationError>>(&f, js.data())
                }
                /// DafnyStandardLibraries-rs.dfy(8464,3)
                pub fn Value(js: &Rc<Value>) -> Rc<Result<Rc<JSON>, Rc<DeserializationError>>> {
                    let mut _source0: Rc<Value> = js.clone();
                    if matches!((&_source0).as_ref(), Null{ .. }) {
                        let mut ___mcc_h0: jnull = _source0.n().clone();
                        Rc::new(Result::Success::<Rc<JSON>, Rc<DeserializationError>> {
                                value: Rc::new(JSON::Null {})
                            })
                    } else {
                        if matches!((&_source0).as_ref(), Bool{ .. }) {
                            let mut ___mcc_h1: jbool = _source0.b().clone();
                            let mut b: jbool = ___mcc_h1.clone();
                            Rc::new(Result::Success::<Rc<JSON>, Rc<DeserializationError>> {
                                    value: Rc::new(JSON::Bool {
                                                b: crate::Std::JSON::Deserializer::_default::Bool(&b)
                                            })
                                })
                        } else {
                            if matches!((&_source0).as_ref(), String{ .. }) {
                                let mut ___mcc_h2: Rc<jstring> = _source0.str().clone();
                                let mut str: Rc<jstring> = ___mcc_h2.clone();
                                let mut valueOrError0: Rc<Result<Sequence<DafnyChar>, Rc<DeserializationError>>> = crate::Std::JSON::Deserializer::_default::String(&str);
                                if valueOrError0.IsFailure() {
                                    valueOrError0.PropagateFailure::<Rc<JSON>>()
                                } else {
                                    let mut s: Sequence<DafnyChar> = valueOrError0.Extract();
                                    Rc::new(Result::Success::<Rc<JSON>, Rc<DeserializationError>> {
                                            value: Rc::new(JSON::String {
                                                        str: s.clone()
                                                    })
                                        })
                                }
                            } else {
                                if matches!((&_source0).as_ref(), Number{ .. }) {
                                    let mut ___mcc_h3: Rc<jnumber> = _source0.num().clone();
                                    let mut dec: Rc<jnumber> = ___mcc_h3.clone();
                                    let mut valueOrError1: Rc<Result<Rc<Decimal>, Rc<DeserializationError>>> = crate::Std::JSON::Deserializer::_default::Number(&dec);
                                    if valueOrError1.IsFailure() {
                                        valueOrError1.PropagateFailure::<Rc<JSON>>()
                                    } else {
                                        let mut n: Rc<Decimal> = valueOrError1.Extract();
                                        Rc::new(Result::Success::<Rc<JSON>, Rc<DeserializationError>> {
                                                value: Rc::new(JSON::Number {
                                                            num: n.clone()
                                                        })
                                            })
                                    }
                                } else {
                                    if matches!((&_source0).as_ref(), Object{ .. }) {
                                        let mut ___mcc_h4: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = _source0.obj().clone();
                                        let mut obj: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = ___mcc_h4.clone();
                                        let mut valueOrError2: Rc<Result<Sequence<(Sequence<DafnyChar>, Rc<JSON>)>, Rc<DeserializationError>>> = crate::Std::JSON::Deserializer::_default::Object(&obj);
                                        if valueOrError2.IsFailure() {
                                            valueOrError2.PropagateFailure::<Rc<JSON>>()
                                        } else {
                                            let mut o: Sequence<(Sequence<DafnyChar>, Rc<JSON>)> = valueOrError2.Extract();
                                            Rc::new(Result::Success::<Rc<JSON>, Rc<DeserializationError>> {
                                                    value: Rc::new(JSON::Object {
                                                                obj: o.clone()
                                                            })
                                                })
                                        }
                                    } else {
                                        let mut ___mcc_h5: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = _source0.arr().clone();
                                        let mut arr: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = ___mcc_h5.clone();
                                        let mut valueOrError3: Rc<Result<Sequence<Rc<JSON>>, Rc<DeserializationError>>> = crate::Std::JSON::Deserializer::_default::Array(&arr);
                                        if valueOrError3.IsFailure() {
                                            valueOrError3.PropagateFailure::<Rc<JSON>>()
                                        } else {
                                            let mut a: Sequence<Rc<JSON>> = valueOrError3.Extract();
                                            Rc::new(Result::Success::<Rc<JSON>, Rc<DeserializationError>> {
                                                    value: Rc::new(JSON::Array {
                                                                arr: a.clone()
                                                            })
                                                })
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8481,3)
                pub fn JSON(js: &Rc<Structural<Rc<Value>>>) -> Rc<Result<Rc<JSON>, Rc<DeserializationError>>> {
                    crate::Std::JSON::Deserializer::_default::Value(js.t())
                }
                /// DafnyStandardLibraries-rs.dfy(8398,3)
                pub fn HEX_TABLE_16() -> Map<u16, crate::Std::JSON::Deserializer::Uint16StrConversion::digit> {
                    crate::Std::JSON::Deserializer::Uint16StrConversion::_default::charToDigit()
                }
                /// DafnyStandardLibraries-rs.dfy(8430,3)
                pub fn DIGITS() -> Map<u8, crate::Std::JSON::ByteStrConversion::digit> {
                    crate::Std::JSON::ByteStrConversion::_default::charToDigit()
                }
                /// DafnyStandardLibraries-rs.dfy(8431,3)
                pub fn MINUS() -> u8 {
                    DafnyChar(char::from_u32(45).unwrap()).0 as u8
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8514,3)
            pub mod Uint16StrConversion {
                pub use ::dafny_runtime::_System::nat;
                pub use ::dafny_runtime::Sequence;
                pub use ::dafny_runtime::seq;
                pub use ::dafny_runtime::int;
                pub use ::dafny_runtime::itertools::Itertools;
                pub use ::std::rc::Rc;
                pub use ::dafny_runtime::DafnyInt;
                pub use ::dafny_runtime::euclidian_modulo;
                pub use ::dafny_runtime::euclidian_division;
                pub use ::dafny_runtime::DafnyChar;
                pub use ::std::primitive::char;
                pub use ::dafny_runtime::Map;
                pub use ::dafny_runtime::map;

                pub struct _default {}

                impl _default {
                    /// DafnyStandardLibraries-rs.dfy(13002,5)
                    pub fn BASE() -> nat {
                        crate::Std::JSON::Deserializer::Uint16StrConversion::_default::base()
                    }
                    /// DafnyStandardLibraries-rs.dfy(13007,5)
                    pub fn IsDigitChar(c: u16) -> bool {
                        crate::Std::JSON::Deserializer::Uint16StrConversion::_default::charToDigit().contains(&c)
                    }
                    /// DafnyStandardLibraries-rs.dfy(13012,5)
                    pub fn OfDigits(digits: &Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>) -> Sequence<u16> {
                        let mut _accumulator: Sequence<u16> = seq![] as Sequence<u16>;
                        let mut _r0 = digits.clone();
                        'TAIL_CALL_START: loop {
                            let digits = _r0;
                            if digits.clone().to_array().len() == 0 {
                                return (seq![] as Sequence<u16>).concat(&_accumulator);
                            } else {
                                _accumulator = seq![crate::Std::JSON::Deserializer::Uint16StrConversion::_default::chars().get(&digits.get(&int!(0)))].concat(&_accumulator);
                                let mut _in0: Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> = digits.drop(&int!(1));
                                _r0 = _in0.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(13022,5)
                    pub fn OfNat(n: &nat) -> Sequence<u16> {
                        if n.clone() == int!(0) {
                            seq![crate::Std::JSON::Deserializer::Uint16StrConversion::_default::chars().get(&int!(0))]
                        } else {
                            crate::Std::JSON::Deserializer::Uint16StrConversion::_default::OfDigits(&crate::Std::JSON::Deserializer::Uint16StrConversion::_default::FromNat(n))
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(13032,5)
                    pub fn IsNumberStr(str: &Sequence<u16>, minus: u16) -> bool {
                        !(!(str.clone().to_array().len() == 0)) || (str.get(&int!(0)) == minus || crate::Std::JSON::Deserializer::Uint16StrConversion::_default::charToDigit().contains(&str.get(&int!(0)))) && Itertools::unique((&str.drop(&int!(1))).iter()).all(({
                                let mut str = str.clone();
                                Rc::new(move |__forall_var_0: u16| -> bool{
            let mut c: u16 = __forall_var_0;
            !str.drop(&int!(1)).contains(&c) || crate::Std::JSON::Deserializer::Uint16StrConversion::_default::IsDigitChar(c)
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                            }).as_ref())
                    }
                    /// DafnyStandardLibraries-rs.dfy(13040,5)
                    pub fn OfInt(n: &DafnyInt, minus: u16) -> Sequence<u16> {
                        if !(n.clone() < int!(0)) {
                            crate::Std::JSON::Deserializer::Uint16StrConversion::_default::OfNat(n)
                        } else {
                            seq![minus].concat(&crate::Std::JSON::Deserializer::Uint16StrConversion::_default::OfNat(&(int!(0) - n.clone())))
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(13050,5)
                    pub fn ToNat(str: &Sequence<u16>) -> nat {
                        if str.clone().to_array().len() == 0 {
                            int!(0)
                        } else {
                            let mut c: u16 = str.get(&(str.cardinality() - int!(1)));
                            crate::Std::JSON::Deserializer::Uint16StrConversion::_default::ToNat(&str.take(&(str.cardinality() - int!(1)))) * crate::Std::JSON::Deserializer::Uint16StrConversion::_default::base() + crate::Std::JSON::Deserializer::Uint16StrConversion::_default::charToDigit().get(&c)
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(13090,5)
                    pub fn ToInt(str: &Sequence<u16>, minus: u16) -> DafnyInt {
                        if seq![minus] <= str.clone() {
                            int!(0) - crate::Std::JSON::Deserializer::Uint16StrConversion::_default::ToNat(&str.drop(&int!(1)))
                        } else {
                            crate::Std::JSON::Deserializer::Uint16StrConversion::_default::ToNat(str)
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(2728,3)
                    pub fn ToNatRight(xs: &Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>) -> nat {
                        if xs.cardinality() == int!(0) {
                            int!(0)
                        } else {
                            crate::Std::JSON::Deserializer::Uint16StrConversion::_default::ToNatRight(&crate::Std::Collections::Seq::_default::DropFirst::<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>(xs)) * crate::Std::JSON::Deserializer::Uint16StrConversion::_default::BASE() + crate::Std::Collections::Seq::_default::First::<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>(xs)
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(2736,3)
                    pub fn ToNatLeft(xs: &Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>) -> nat {
                        let mut _accumulator: nat = int!(0);
                        let mut _r0 = xs.clone();
                        'TAIL_CALL_START: loop {
                            let xs = _r0;
                            if xs.cardinality() == int!(0) {
                                return int!(0) + _accumulator.clone();
                            } else {
                                _accumulator = crate::Std::Collections::Seq::_default::Last::<DafnyInt>(&xs) * crate::Std::Arithmetic::Power::_default::Pow(&crate::Std::JSON::Deserializer::Uint16StrConversion::_default::BASE(), &(xs.cardinality() - int!(1))) + _accumulator.clone();
                                let mut _in0: Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> = crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>(&xs);
                                _r0 = _in0.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(3020,3)
                    pub fn FromNat(n: &nat) -> Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> {
                        let mut _accumulator: Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> = seq![] as Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>;
                        let mut _r0 = n.clone();
                        'TAIL_CALL_START: loop {
                            let n = _r0;
                            if n.clone() == int!(0) {
                                return _accumulator.concat(&(seq![] as Sequence<DafnyInt>));
                            } else {
                                _accumulator = _accumulator.concat(&seq![euclidian_modulo(n.clone(), crate::Std::JSON::Deserializer::Uint16StrConversion::_default::BASE())]);
                                let mut _in0: DafnyInt = euclidian_division(n.clone(), crate::Std::JSON::Deserializer::Uint16StrConversion::_default::BASE());
                                _r0 = _in0.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(3104,3)
                    pub fn SeqExtend(xs: &Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>, n: &nat) -> Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> {
                        let mut _r0 = xs.clone();
                        let mut _r1 = n.clone();
                        'TAIL_CALL_START: loop {
                            let xs = _r0;
                            let n = _r1;
                            if !(xs.cardinality() < n.clone()) {
                                return xs.clone();
                            } else {
                                let mut _in0: Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> = xs.concat(&seq![int!(0)]);
                                let mut _in1: nat = n.clone();
                                _r0 = _in0.clone();
                                _r1 = _in1.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(3116,3)
                    pub fn SeqExtendMultiple(xs: &Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>, n: &nat) -> Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> {
                        let mut newLen: DafnyInt = xs.cardinality() + n.clone() - euclidian_modulo(xs.cardinality(), n.clone());
                        crate::Std::JSON::Deserializer::Uint16StrConversion::_default::SeqExtend(xs, &newLen)
                    }
                    /// DafnyStandardLibraries-rs.dfy(3130,3)
                    pub fn FromNatWithLen(n: &nat, len: &nat) -> Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> {
                        crate::Std::JSON::Deserializer::Uint16StrConversion::_default::SeqExtend(&crate::Std::JSON::Deserializer::Uint16StrConversion::_default::FromNat(n), len)
                    }
                    /// DafnyStandardLibraries-rs.dfy(3153,3)
                    pub fn SeqZero(len: &nat) -> Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> {
                        let mut xs: Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> = crate::Std::JSON::Deserializer::Uint16StrConversion::_default::FromNatWithLen(&int!(0), len);
                        xs.clone()
                    }
                    /// DafnyStandardLibraries-rs.dfy(3182,3)
                    pub fn SeqAdd(xs: &Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>, ys: &Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>) -> (Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>, nat) {
                        if xs.cardinality() == int!(0) {
                            (
                                seq![] as Sequence<DafnyInt>,
                                int!(0)
                            )
                        } else {
                            let mut __let_tmp_rhs0: (Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>, nat) = crate::Std::JSON::Deserializer::Uint16StrConversion::_default::SeqAdd(&crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>(xs), &crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>(ys));
                            let mut _zs_k: Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> = __let_tmp_rhs0.0.clone();
                            let mut cin: nat = __let_tmp_rhs0.1.clone();
                            let mut sum: DafnyInt = crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) + crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) + cin.clone();
                            let mut __let_tmp_rhs1: (DafnyInt, DafnyInt) = if sum.clone() < crate::Std::JSON::Deserializer::Uint16StrConversion::_default::BASE() {
                                    (
                                        sum.clone(),
                                        int!(0)
                                    )
                                } else {
                                    (
                                        sum.clone() - crate::Std::JSON::Deserializer::Uint16StrConversion::_default::BASE(),
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
                    pub fn SeqSub(xs: &Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>, ys: &Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>) -> (Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>, nat) {
                        if xs.cardinality() == int!(0) {
                            (
                                seq![] as Sequence<DafnyInt>,
                                int!(0)
                            )
                        } else {
                            let mut __let_tmp_rhs0: (Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>, nat) = crate::Std::JSON::Deserializer::Uint16StrConversion::_default::SeqSub(&crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>(xs), &crate::Std::Collections::Seq::_default::DropLast::<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>(ys));
                            let mut zs: Sequence<crate::Std::JSON::Deserializer::Uint16StrConversion::digit> = __let_tmp_rhs0.0.clone();
                            let mut cin: nat = __let_tmp_rhs0.1.clone();
                            let mut __let_tmp_rhs1: (DafnyInt, DafnyInt) = if !(crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) < crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) + cin.clone()) {
                                    (
                                        crate::Std::Collections::Seq::_default::Last::<DafnyInt>(xs) - crate::Std::Collections::Seq::_default::Last::<DafnyInt>(ys) - cin.clone(),
                                        int!(0)
                                    )
                                } else {
                                    (
                                        crate::Std::JSON::Deserializer::Uint16StrConversion::_default::BASE() + crate::Std::Collections::Seq::_default::Last::<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>(xs) - crate::Std::Collections::Seq::_default::Last::<crate::Std::JSON::Deserializer::Uint16StrConversion::digit>(ys) - cin.clone(),
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
                    /// DafnyStandardLibraries-rs.dfy(8516,5)
                    pub fn chars() -> crate::Std::JSON::Deserializer::Uint16StrConversion::CharSeq {
                        seq![DafnyChar(char::from_u32(48).unwrap()).0 as u16, DafnyChar(char::from_u32(49).unwrap()).0 as u16, DafnyChar(char::from_u32(50).unwrap()).0 as u16, DafnyChar(char::from_u32(51).unwrap()).0 as u16, DafnyChar(char::from_u32(52).unwrap()).0 as u16, DafnyChar(char::from_u32(53).unwrap()).0 as u16, DafnyChar(char::from_u32(54).unwrap()).0 as u16, DafnyChar(char::from_u32(55).unwrap()).0 as u16, DafnyChar(char::from_u32(56).unwrap()).0 as u16, DafnyChar(char::from_u32(57).unwrap()).0 as u16, DafnyChar(char::from_u32(97).unwrap()).0 as u16, DafnyChar(char::from_u32(98).unwrap()).0 as u16, DafnyChar(char::from_u32(99).unwrap()).0 as u16, DafnyChar(char::from_u32(100).unwrap()).0 as u16, DafnyChar(char::from_u32(101).unwrap()).0 as u16, DafnyChar(char::from_u32(102).unwrap()).0 as u16, DafnyChar(char::from_u32(65).unwrap()).0 as u16, DafnyChar(char::from_u32(66).unwrap()).0 as u16, DafnyChar(char::from_u32(67).unwrap()).0 as u16, DafnyChar(char::from_u32(68).unwrap()).0 as u16, DafnyChar(char::from_u32(69).unwrap()).0 as u16, DafnyChar(char::from_u32(70).unwrap()).0 as u16]
                    }
                    /// DafnyStandardLibraries-rs.dfy(12996,5)
                    pub fn base() -> DafnyInt {
                        crate::Std::JSON::Deserializer::Uint16StrConversion::_default::chars().cardinality()
                    }
                    /// DafnyStandardLibraries-rs.dfy(8517,5)
                    pub fn charToDigit() -> Map<u16, crate::Std::JSON::Deserializer::Uint16StrConversion::digit> {
                        map![DafnyChar(char::from_u32(48).unwrap()).0 as u16 => int!(0), DafnyChar(char::from_u32(49).unwrap()).0 as u16 => int!(1), DafnyChar(char::from_u32(50).unwrap()).0 as u16 => int!(2), DafnyChar(char::from_u32(51).unwrap()).0 as u16 => int!(3), DafnyChar(char::from_u32(52).unwrap()).0 as u16 => int!(4), DafnyChar(char::from_u32(53).unwrap()).0 as u16 => int!(5), DafnyChar(char::from_u32(54).unwrap()).0 as u16 => int!(6), DafnyChar(char::from_u32(55).unwrap()).0 as u16 => int!(7), DafnyChar(char::from_u32(56).unwrap()).0 as u16 => int!(8), DafnyChar(char::from_u32(57).unwrap()).0 as u16 => int!(9), DafnyChar(char::from_u32(97).unwrap()).0 as u16 => int!(10), DafnyChar(char::from_u32(98).unwrap()).0 as u16 => int!(11), DafnyChar(char::from_u32(99).unwrap()).0 as u16 => int!(12), DafnyChar(char::from_u32(100).unwrap()).0 as u16 => int!(13), DafnyChar(char::from_u32(101).unwrap()).0 as u16 => int!(14), DafnyChar(char::from_u32(102).unwrap()).0 as u16 => int!(15), DafnyChar(char::from_u32(65).unwrap()).0 as u16 => int!(10), DafnyChar(char::from_u32(66).unwrap()).0 as u16 => int!(11), DafnyChar(char::from_u32(67).unwrap()).0 as u16 => int!(12), DafnyChar(char::from_u32(68).unwrap()).0 as u16 => int!(13), DafnyChar(char::from_u32(69).unwrap()).0 as u16 => int!(14), DafnyChar(char::from_u32(70).unwrap()).0 as u16 => int!(15)]
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(13106,5)
                pub type CharSeq = Sequence<u16>;

                /// DafnyStandardLibraries-rs.dfy(3285,3)
                pub type digit = DafnyInt;
            }
        }

        /// DafnyStandardLibraries-rs.dfy(8528,1)
        pub mod Errors {
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::std::rc::Rc;
            pub use crate::Std::JSON::Errors::DeserializationError::UnterminatedSequence;
            pub use ::dafny_runtime::string_of;
            pub use crate::Std::JSON::Errors::DeserializationError::UnsupportedEscape;
            pub use crate::Std::JSON::Errors::DeserializationError::EscapeAtEOS;
            pub use crate::Std::JSON::Errors::DeserializationError::EmptyNumber;
            pub use crate::Std::JSON::Errors::DeserializationError::ExpectingEOF;
            pub use crate::Std::JSON::Errors::DeserializationError::IntOverflow;
            pub use crate::Std::JSON::Errors::DeserializationError::ReachedEOF;
            pub use crate::Std::JSON::Errors::DeserializationError::ExpectingByte;
            pub use ::dafny_runtime::truncate;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::seq;
            pub use crate::Std::JSON::Errors::DeserializationError::ExpectingAnyByte;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::dafny_runtime::integer_range;
            pub use ::dafny_runtime::Zero;
            pub use ::std::fmt::Debug;
            pub use ::std::fmt::Formatter;
            pub use ::std::fmt::Result;
            pub use ::dafny_runtime::DafnyPrint;
            pub use ::std::cmp::PartialEq;
            pub use ::std::cmp::Eq;
            pub use ::std::hash::Hash;
            pub use ::std::hash::Hasher;
            pub use ::std::convert::AsRef;
            pub use crate::Std::JSON::Errors::SerializationError::OutOfMemory;
            pub use crate::Std::JSON::Errors::SerializationError::IntTooLarge;
            pub use crate::Std::Strings::_default;
            pub use crate::Std::JSON::Errors::SerializationError::StringTooLong;

            /// DafnyStandardLibraries-rs.dfy(8535,3)
            #[derive(Clone)]
            pub enum DeserializationError {
                UnterminatedSequence {},
                UnsupportedEscape {
                    str: Sequence<DafnyChar>
                },
                EscapeAtEOS {},
                EmptyNumber {},
                ExpectingEOF {},
                IntOverflow {},
                ReachedEOF {},
                ExpectingByte {
                    expected: u8,
                    b: i16
                },
                ExpectingAnyByte {
                    expected_sq: Sequence<u8>,
                    b: i16
                },
                InvalidUnicode {
                    str: Sequence<DafnyChar>
                }
            }

            impl DeserializationError {
                /// DafnyStandardLibraries-rs.dfy(8536,5)
                pub fn ToString(&self) -> Sequence<DafnyChar> {
                    let mut _source0: Rc<crate::Std::JSON::Errors::DeserializationError> = Rc::new(self.clone());
                    if matches!((&_source0).as_ref(), UnterminatedSequence{ .. }) {
                        string_of("Unterminated sequence")
                    } else {
                        if matches!((&_source0).as_ref(), UnsupportedEscape{ .. }) {
                            let mut ___mcc_h0: Sequence<DafnyChar> = _source0.str().clone();
                            let mut str: Sequence<DafnyChar> = ___mcc_h0.clone();
                            string_of("Unsupported escape sequence: ").concat(&str)
                        } else {
                            if matches!((&_source0).as_ref(), EscapeAtEOS{ .. }) {
                                string_of("Escape character at end of string")
                            } else {
                                if matches!((&_source0).as_ref(), EmptyNumber{ .. }) {
                                    string_of("Number must contain at least one digit")
                                } else {
                                    if matches!((&_source0).as_ref(), ExpectingEOF{ .. }) {
                                        string_of("Expecting EOF")
                                    } else {
                                        if matches!((&_source0).as_ref(), IntOverflow{ .. }) {
                                            string_of("Input length does not fit in a 32-bit counter")
                                        } else {
                                            if matches!((&_source0).as_ref(), ReachedEOF{ .. }) {
                                                string_of("Reached EOF")
                                            } else {
                                                if matches!((&_source0).as_ref(), ExpectingByte{ .. }) {
                                                    let mut ___mcc_h1: u8 = _source0.expected().clone();
                                                    let mut ___mcc_h2: i16 = _source0.b().clone();
                                                    let mut b: i16 = ___mcc_h2;
                                                    let mut b0: u8 = ___mcc_h1;
                                                    let mut c: Sequence<DafnyChar> = if truncate!(int!(0), i16) < b {
                                                            string_of("'").concat(&seq![DafnyChar(b as char)]).concat(&string_of("'"))
                                                        } else {
                                                            string_of("EOF")
                                                        };
                                                    string_of("Expecting '").concat(&seq![DafnyChar(b0 as char)]).concat(&string_of("', read ")).concat(&c)
                                                } else {
                                                    if matches!((&_source0).as_ref(), ExpectingAnyByte{ .. }) {
                                                        let mut ___mcc_h3: Sequence<u8> = _source0.expected_sq().clone();
                                                        let mut ___mcc_h4: i16 = _source0.b().clone();
                                                        let mut b: i16 = ___mcc_h4;
                                                        let mut bs0: Sequence<u8> = ___mcc_h3.clone();
                                                        let mut c: Sequence<DafnyChar> = if truncate!(int!(0), i16) < b {
                                                                string_of("'").concat(&seq![DafnyChar(b as char)]).concat(&string_of("'"))
                                                            } else {
                                                                string_of("EOF")
                                                            };
                                                        let mut c0s: Sequence<DafnyChar> = {
                                                                let _initializer = {
                                                                        let bs0: Sequence<u8> = bs0.clone();
                                                                        {
                                                                            let mut bs0 = bs0.clone();
                                                                            Rc::new(move |idx: &DafnyInt| -> DafnyChar{
            DafnyChar(bs0.get(idx) as char)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                                                        }
                                                                    };
                                                                integer_range(Zero::zero(), bs0.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                                                            };
                                                        string_of("Expecting one of '").concat(&c0s).concat(&string_of("', read ")).concat(&c)
                                                    } else {
                                                        let mut ___mcc_h5: Sequence<DafnyChar> = _source0.str().clone();
                                                        let mut str: Sequence<DafnyChar> = ___mcc_h5.clone();
                                                        if str.clone() == string_of("") {
                                                            string_of("Invalid Unicode sequence")
                                                        } else {
                                                            str.clone()
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
                /// Gets the field str for all enum members which have it
                pub fn str(&self) -> &Sequence<DafnyChar> {
                    match self {
                        DeserializationError::UnterminatedSequence{} => panic!("field does not exist on this variant"),
                        DeserializationError::UnsupportedEscape{str, } => str,
                        DeserializationError::EscapeAtEOS{} => panic!("field does not exist on this variant"),
                        DeserializationError::EmptyNumber{} => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingEOF{} => panic!("field does not exist on this variant"),
                        DeserializationError::IntOverflow{} => panic!("field does not exist on this variant"),
                        DeserializationError::ReachedEOF{} => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingByte{expected, b, } => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingAnyByte{expected_sq, b, } => panic!("field does not exist on this variant"),
                        DeserializationError::InvalidUnicode{str, } => str,
                    }
                }
                /// Gets the field expected for all enum members which have it
                pub fn expected(&self) -> &u8 {
                    match self {
                        DeserializationError::UnterminatedSequence{} => panic!("field does not exist on this variant"),
                        DeserializationError::UnsupportedEscape{str, } => panic!("field does not exist on this variant"),
                        DeserializationError::EscapeAtEOS{} => panic!("field does not exist on this variant"),
                        DeserializationError::EmptyNumber{} => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingEOF{} => panic!("field does not exist on this variant"),
                        DeserializationError::IntOverflow{} => panic!("field does not exist on this variant"),
                        DeserializationError::ReachedEOF{} => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingByte{expected, b, } => expected,
                        DeserializationError::ExpectingAnyByte{expected_sq, b, } => panic!("field does not exist on this variant"),
                        DeserializationError::InvalidUnicode{str, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field b for all enum members which have it
                pub fn b(&self) -> &i16 {
                    match self {
                        DeserializationError::UnterminatedSequence{} => panic!("field does not exist on this variant"),
                        DeserializationError::UnsupportedEscape{str, } => panic!("field does not exist on this variant"),
                        DeserializationError::EscapeAtEOS{} => panic!("field does not exist on this variant"),
                        DeserializationError::EmptyNumber{} => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingEOF{} => panic!("field does not exist on this variant"),
                        DeserializationError::IntOverflow{} => panic!("field does not exist on this variant"),
                        DeserializationError::ReachedEOF{} => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingByte{expected, b, } => b,
                        DeserializationError::ExpectingAnyByte{expected_sq, b, } => b,
                        DeserializationError::InvalidUnicode{str, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field expected_sq for all enum members which have it
                pub fn expected_sq(&self) -> &Sequence<u8> {
                    match self {
                        DeserializationError::UnterminatedSequence{} => panic!("field does not exist on this variant"),
                        DeserializationError::UnsupportedEscape{str, } => panic!("field does not exist on this variant"),
                        DeserializationError::EscapeAtEOS{} => panic!("field does not exist on this variant"),
                        DeserializationError::EmptyNumber{} => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingEOF{} => panic!("field does not exist on this variant"),
                        DeserializationError::IntOverflow{} => panic!("field does not exist on this variant"),
                        DeserializationError::ReachedEOF{} => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingByte{expected, b, } => panic!("field does not exist on this variant"),
                        DeserializationError::ExpectingAnyByte{expected_sq, b, } => expected_sq,
                        DeserializationError::InvalidUnicode{str, } => panic!("field does not exist on this variant"),
                    }
                }
            }

            impl Debug
                for DeserializationError {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for DeserializationError {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        DeserializationError::UnterminatedSequence{} => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.UnterminatedSequence")?;
                            Ok(())
                        },
                        DeserializationError::UnsupportedEscape{str, } => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.UnsupportedEscape(")?;
                            DafnyPrint::fmt_print(str, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        DeserializationError::EscapeAtEOS{} => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.EscapeAtEOS")?;
                            Ok(())
                        },
                        DeserializationError::EmptyNumber{} => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.EmptyNumber")?;
                            Ok(())
                        },
                        DeserializationError::ExpectingEOF{} => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.ExpectingEOF")?;
                            Ok(())
                        },
                        DeserializationError::IntOverflow{} => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.IntOverflow")?;
                            Ok(())
                        },
                        DeserializationError::ReachedEOF{} => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.ReachedEOF")?;
                            Ok(())
                        },
                        DeserializationError::ExpectingByte{expected, b, } => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.ExpectingByte(")?;
                            DafnyPrint::fmt_print(expected, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(b, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        DeserializationError::ExpectingAnyByte{expected_sq, b, } => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.ExpectingAnyByte(")?;
                            DafnyPrint::fmt_print(expected_sq, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(b, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        DeserializationError::InvalidUnicode{str, } => {
                            write!(_formatter, "Std.JSON.Errors.DeserializationError.InvalidUnicode(")?;
                            DafnyPrint::fmt_print(str, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for DeserializationError {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (DeserializationError::UnterminatedSequence{}, DeserializationError::UnterminatedSequence{}) => {
                            true
                        },
                        (DeserializationError::UnsupportedEscape{str, }, DeserializationError::UnsupportedEscape{str: _2_str, }) => {
                            str == _2_str
                        },
                        (DeserializationError::EscapeAtEOS{}, DeserializationError::EscapeAtEOS{}) => {
                            true
                        },
                        (DeserializationError::EmptyNumber{}, DeserializationError::EmptyNumber{}) => {
                            true
                        },
                        (DeserializationError::ExpectingEOF{}, DeserializationError::ExpectingEOF{}) => {
                            true
                        },
                        (DeserializationError::IntOverflow{}, DeserializationError::IntOverflow{}) => {
                            true
                        },
                        (DeserializationError::ReachedEOF{}, DeserializationError::ReachedEOF{}) => {
                            true
                        },
                        (DeserializationError::ExpectingByte{expected, b, }, DeserializationError::ExpectingByte{expected: _2_expected, b: _2_b, }) => {
                            expected == _2_expected && b == _2_b
                        },
                        (DeserializationError::ExpectingAnyByte{expected_sq, b, }, DeserializationError::ExpectingAnyByte{expected_sq: _2_expected_sq, b: _2_b, }) => {
                            expected_sq == _2_expected_sq && b == _2_b
                        },
                        (DeserializationError::InvalidUnicode{str, }, DeserializationError::InvalidUnicode{str: _2_str, }) => {
                            str == _2_str
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for DeserializationError {}

            impl Hash
                for DeserializationError {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        DeserializationError::UnterminatedSequence{} => {
                            
                        },
                        DeserializationError::UnsupportedEscape{str, } => {
                            Hash::hash(str, _state)
                        },
                        DeserializationError::EscapeAtEOS{} => {
                            
                        },
                        DeserializationError::EmptyNumber{} => {
                            
                        },
                        DeserializationError::ExpectingEOF{} => {
                            
                        },
                        DeserializationError::IntOverflow{} => {
                            
                        },
                        DeserializationError::ReachedEOF{} => {
                            
                        },
                        DeserializationError::ExpectingByte{expected, b, } => {
                            Hash::hash(expected, _state);
                            Hash::hash(b, _state)
                        },
                        DeserializationError::ExpectingAnyByte{expected_sq, b, } => {
                            Hash::hash(expected_sq, _state);
                            Hash::hash(b, _state)
                        },
                        DeserializationError::InvalidUnicode{str, } => {
                            Hash::hash(str, _state)
                        },
                    }
                }
            }

            impl AsRef<DeserializationError>
                for DeserializationError {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8568,3)
            #[derive(Clone)]
            pub enum SerializationError {
                OutOfMemory {},
                IntTooLarge {
                    i: DafnyInt
                },
                StringTooLong {
                    s: Sequence<DafnyChar>
                },
                InvalidUnicode {}
            }

            impl SerializationError {
                /// DafnyStandardLibraries-rs.dfy(8569,5)
                pub fn ToString(&self) -> Sequence<DafnyChar> {
                    let mut _source0: Rc<crate::Std::JSON::Errors::SerializationError> = Rc::new(self.clone());
                    if matches!((&_source0).as_ref(), OutOfMemory{ .. }) {
                        string_of("Out of memory")
                    } else {
                        if matches!((&_source0).as_ref(), IntTooLarge{ .. }) {
                            let mut ___mcc_h0: DafnyInt = _source0.i().clone();
                            let mut i: DafnyInt = ___mcc_h0.clone();
                            string_of("Integer too large: ").concat(&_default::OfInt(&i))
                        } else {
                            if matches!((&_source0).as_ref(), StringTooLong{ .. }) {
                                let mut ___mcc_h1: Sequence<DafnyChar> = _source0.s().clone();
                                let mut s: Sequence<DafnyChar> = ___mcc_h1.clone();
                                string_of("String too long: ").concat(&s)
                            } else {
                                string_of("Invalid Unicode sequence")
                            }
                        }
                    }
                }
                /// Gets the field i for all enum members which have it
                pub fn i(&self) -> &DafnyInt {
                    match self {
                        SerializationError::OutOfMemory{} => panic!("field does not exist on this variant"),
                        SerializationError::IntTooLarge{i, } => i,
                        SerializationError::StringTooLong{s, } => panic!("field does not exist on this variant"),
                        SerializationError::InvalidUnicode{} => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field s for all enum members which have it
                pub fn s(&self) -> &Sequence<DafnyChar> {
                    match self {
                        SerializationError::OutOfMemory{} => panic!("field does not exist on this variant"),
                        SerializationError::IntTooLarge{i, } => panic!("field does not exist on this variant"),
                        SerializationError::StringTooLong{s, } => s,
                        SerializationError::InvalidUnicode{} => panic!("field does not exist on this variant"),
                    }
                }
            }

            impl Debug
                for SerializationError {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for SerializationError {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        SerializationError::OutOfMemory{} => {
                            write!(_formatter, "Std.JSON.Errors.SerializationError.OutOfMemory")?;
                            Ok(())
                        },
                        SerializationError::IntTooLarge{i, } => {
                            write!(_formatter, "Std.JSON.Errors.SerializationError.IntTooLarge(")?;
                            DafnyPrint::fmt_print(i, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        SerializationError::StringTooLong{s, } => {
                            write!(_formatter, "Std.JSON.Errors.SerializationError.StringTooLong(")?;
                            DafnyPrint::fmt_print(s, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        SerializationError::InvalidUnicode{} => {
                            write!(_formatter, "Std.JSON.Errors.SerializationError.InvalidUnicode")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for SerializationError {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (SerializationError::OutOfMemory{}, SerializationError::OutOfMemory{}) => {
                            true
                        },
                        (SerializationError::IntTooLarge{i, }, SerializationError::IntTooLarge{i: _2_i, }) => {
                            i == _2_i
                        },
                        (SerializationError::StringTooLong{s, }, SerializationError::StringTooLong{s: _2_s, }) => {
                            s == _2_s
                        },
                        (SerializationError::InvalidUnicode{}, SerializationError::InvalidUnicode{}) => {
                            true
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for SerializationError {}

            impl Hash
                for SerializationError {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        SerializationError::OutOfMemory{} => {
                            
                        },
                        SerializationError::IntTooLarge{i, } => {
                            Hash::hash(i, _state)
                        },
                        SerializationError::StringTooLong{s, } => {
                            Hash::hash(s, _state)
                        },
                        SerializationError::InvalidUnicode{} => {
                            
                        },
                    }
                }
            }

            impl AsRef<SerializationError>
                for SerializationError {
                fn as_ref(&self) -> &Self {
                    self
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(8588,1)
        pub mod Grammar {
            pub use ::dafny_runtime::truncate;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::std::primitive::char;
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::seq;
            pub use crate::Std::JSON::Utils::Views::Core::View;
            pub use crate::Std::JSON::Utils::Views::Core::View_;
            pub use ::std::rc::Rc;
            pub use ::dafny_runtime::DafnyType;
            pub use ::std::fmt::Debug;
            pub use ::std::fmt::Formatter;
            pub use ::std::fmt::Result;
            pub use ::dafny_runtime::DafnyPrint;
            pub use ::dafny_runtime::upcast_id;
            pub use ::std::cmp::Eq;
            pub use ::std::hash::Hash;
            pub use ::std::cmp::PartialEq;
            pub use ::std::hash::Hasher;
            pub use ::std::convert::AsRef;
            pub use ::dafny_runtime::rc_coerce;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(8601,3)
                pub fn _Blank_q(b: u8) -> bool {
                    b == truncate!(int!(32), u8) || b == truncate!(int!(9), u8) || b == truncate!(int!(10), u8) || b == truncate!(int!(13), u8)
                }
                /// DafnyStandardLibraries-rs.dfy(8632,3)
                pub fn _Digit_q(b: u8) -> bool {
                    !(b < DafnyChar(char::from_u32(48).unwrap()).0 as u8) && !((DafnyChar(char::from_u32(57).unwrap()).0 as u8) < b)
                }
                /// DafnyStandardLibraries-rs.dfy(8618,3)
                pub fn NULL() -> Sequence<u8> {
                    seq![DafnyChar(char::from_u32(110).unwrap()).0 as u8, DafnyChar(char::from_u32(117).unwrap()).0 as u8, DafnyChar(char::from_u32(108).unwrap()).0 as u8, DafnyChar(char::from_u32(108).unwrap()).0 as u8]
                }
                /// DafnyStandardLibraries-rs.dfy(8619,3)
                pub fn TRUE() -> Sequence<u8> {
                    seq![DafnyChar(char::from_u32(116).unwrap()).0 as u8, DafnyChar(char::from_u32(114).unwrap()).0 as u8, DafnyChar(char::from_u32(117).unwrap()).0 as u8, DafnyChar(char::from_u32(101).unwrap()).0 as u8]
                }
                /// DafnyStandardLibraries-rs.dfy(8620,3)
                pub fn FALSE() -> Sequence<u8> {
                    seq![DafnyChar(char::from_u32(102).unwrap()).0 as u8, DafnyChar(char::from_u32(97).unwrap()).0 as u8, DafnyChar(char::from_u32(108).unwrap()).0 as u8, DafnyChar(char::from_u32(115).unwrap()).0 as u8, DafnyChar(char::from_u32(101).unwrap()).0 as u8]
                }
                /// DafnyStandardLibraries-rs.dfy(8590,3)
                pub fn DOUBLEQUOTE() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(34).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8591,3)
                pub fn PERIOD() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(46).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8592,3)
                pub fn E() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(101).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8593,3)
                pub fn COLON() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(58).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8594,3)
                pub fn COMMA() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(44).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8595,3)
                pub fn LBRACE() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(123).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8596,3)
                pub fn RBRACE() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(125).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8597,3)
                pub fn LBRACKET() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(91).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8598,3)
                pub fn RBRACKET() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(93).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8599,3)
                pub fn MINUS() -> View {
                    View_::OfBytes(&seq![DafnyChar(char::from_u32(45).unwrap()).0 as u8])
                }
                /// DafnyStandardLibraries-rs.dfy(8589,3)
                pub fn EMPTY() -> View {
                    View_::OfBytes(&(seq![] as Sequence<u8>))
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8658,3)
            pub type jchar = Rc<View_>;

            /// An element of jchar
            pub fn __init_jchar() -> Rc<View_> {
                View_::OfBytes(&seq![DafnyChar(char::from_u32(98).unwrap()).0 as u8])
            }

            /// DafnyStandardLibraries-rs.dfy(8662,3)
            pub type jquote = Rc<View_>;

            /// An element of jquote
            pub fn __init_jquote() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::DOUBLEQUOTE()
            }

            /// DafnyStandardLibraries-rs.dfy(8666,3)
            pub type jperiod = Rc<View_>;

            /// An element of jperiod
            pub fn __init_jperiod() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::PERIOD()
            }

            /// DafnyStandardLibraries-rs.dfy(8670,3)
            pub type je = Rc<View_>;

            /// An element of je
            pub fn __init_je() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::E()
            }

            /// DafnyStandardLibraries-rs.dfy(8674,3)
            pub type jcolon = Rc<View_>;

            /// An element of jcolon
            pub fn __init_jcolon() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::COLON()
            }

            /// DafnyStandardLibraries-rs.dfy(8678,3)
            pub type jcomma = Rc<View_>;

            /// An element of jcomma
            pub fn __init_jcomma() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::COMMA()
            }

            /// DafnyStandardLibraries-rs.dfy(8682,3)
            pub type jlbrace = Rc<View_>;

            /// An element of jlbrace
            pub fn __init_jlbrace() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::LBRACE()
            }

            /// DafnyStandardLibraries-rs.dfy(8686,3)
            pub type jrbrace = Rc<View_>;

            /// An element of jrbrace
            pub fn __init_jrbrace() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::RBRACE()
            }

            /// DafnyStandardLibraries-rs.dfy(8690,3)
            pub type jlbracket = Rc<View_>;

            /// An element of jlbracket
            pub fn __init_jlbracket() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::LBRACKET()
            }

            /// DafnyStandardLibraries-rs.dfy(8694,3)
            pub type jrbracket = Rc<View_>;

            /// An element of jrbracket
            pub fn __init_jrbracket() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::RBRACKET()
            }

            /// DafnyStandardLibraries-rs.dfy(8698,3)
            pub type jminus = Rc<View_>;

            /// An element of jminus
            pub fn __init_jminus() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::MINUS()
            }

            /// DafnyStandardLibraries-rs.dfy(8702,3)
            pub type jsign = Rc<View_>;

            /// An element of jsign
            pub fn __init_jsign() -> Rc<View_> {
                crate::Std::JSON::Grammar::_default::EMPTY()
            }

            /// DafnyStandardLibraries-rs.dfy(8706,3)
            pub type jblanks = Rc<View_>;

            /// An element of jblanks
            pub fn __init_jblanks() -> Rc<View_> {
                View_::OfBytes(&(seq![] as Sequence<u8>))
            }

            /// DafnyStandardLibraries-rs.dfy(8710,3)
            #[derive(Clone)]
            pub enum Structural<T: DafnyType> {
                Structural {
                    before: crate::Std::JSON::Grammar::jblanks,
                    t: T,
                    after: crate::Std::JSON::Grammar::jblanks
                }
            }

            impl<T: DafnyType> Structural<T> {
                /// Returns a borrow of the field before
                pub fn before(&self) -> &crate::Std::JSON::Grammar::jblanks {
                    match self {
                        Structural::Structural{before, t, after, } => before,
                    }
                }
                /// Returns a borrow of the field t
                pub fn t(&self) -> &T {
                    match self {
                        Structural::Structural{before, t, after, } => t,
                    }
                }
                /// Returns a borrow of the field after
                pub fn after(&self) -> &crate::Std::JSON::Grammar::jblanks {
                    match self {
                        Structural::Structural{before, t, after, } => after,
                    }
                }
            }

            impl<T: DafnyType> Debug
                for Structural<T> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<T: DafnyType> DafnyPrint
                for Structural<T> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        Structural::Structural{before, t, after, } => {
                            write!(_formatter, "Std.JSON.Grammar.Structural.Structural(")?;
                            DafnyPrint::fmt_print(before, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(t, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(after, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<T: DafnyType> Structural<T> {
                /// Given type parameter conversions, returns a lambda to convert this structure
                pub fn coerce<__T0: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T) -> __T0 + 'static>) -> Rc<impl ::std::ops::Fn(Structural<T>) -> Structural<__T0>> {
                    Rc::new(move |this: Self| -> Structural<__T0>{
                            match this {
                                Structural::Structural{before, t, after, } => {
                                    Structural::Structural {
                                        before: upcast_id::<crate::Std::JSON::Grammar::jblanks>()(before),
                                        t: f_0.clone()(t),
                                        after: upcast_id::<crate::Std::JSON::Grammar::jblanks>()(after)
                                    }
                                },
                            }
                        })
                }
            }

            impl<T: DafnyType + Eq + Hash> PartialEq
                for Structural<T> {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (Structural::Structural{before, t, after, }, Structural::Structural{before: _2_before, t: _2_t, after: _2_after, }) => {
                            before == _2_before && t == _2_t && after == _2_after
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl<T: DafnyType + Eq + Hash> Eq
                for Structural<T> {}

            impl<T: DafnyType + Hash> Hash
                for Structural<T> {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        Structural::Structural{before, t, after, } => {
                            Hash::hash(before, _state);
                            Hash::hash(t, _state);
                            Hash::hash(after, _state)
                        },
                    }
                }
            }

            impl<T: DafnyType> AsRef<Structural<T>>
                for Structural<T> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8712,3)
            #[derive(Clone)]
            pub enum Maybe<T: DafnyType> {
                Empty {},
                NonEmpty {
                    t: T
                }
            }

            impl<T: DafnyType> Maybe<T> {
                /// Gets the field t for all enum members which have it
                pub fn t(&self) -> &T {
                    match self {
                        Maybe::Empty{} => panic!("field does not exist on this variant"),
                        Maybe::NonEmpty{t, } => t,
                    }
                }
            }

            impl<T: DafnyType> Debug
                for Maybe<T> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<T: DafnyType> DafnyPrint
                for Maybe<T> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        Maybe::Empty{} => {
                            write!(_formatter, "Std.JSON.Grammar.Maybe.Empty")?;
                            Ok(())
                        },
                        Maybe::NonEmpty{t, } => {
                            write!(_formatter, "Std.JSON.Grammar.Maybe.NonEmpty(")?;
                            DafnyPrint::fmt_print(t, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<T: DafnyType> Maybe<T> {
                /// Given type parameter conversions, returns a lambda to convert this structure
                pub fn coerce<__T0: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T) -> __T0 + 'static>) -> Rc<impl ::std::ops::Fn(Maybe<T>) -> Maybe<__T0>> {
                    Rc::new(move |this: Self| -> Maybe<__T0>{
                            match this {
                                Maybe::Empty{} => {
                                    Maybe::Empty {}
                                },
                                Maybe::NonEmpty{t, } => {
                                    Maybe::NonEmpty {
                                        t: f_0.clone()(t)
                                    }
                                },
                            }
                        })
                }
            }

            impl<T: DafnyType + Eq + Hash> PartialEq
                for Maybe<T> {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (Maybe::Empty{}, Maybe::Empty{}) => {
                            true
                        },
                        (Maybe::NonEmpty{t, }, Maybe::NonEmpty{t: _2_t, }) => {
                            t == _2_t
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl<T: DafnyType + Eq + Hash> Eq
                for Maybe<T> {}

            impl<T: DafnyType + Hash> Hash
                for Maybe<T> {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        Maybe::Empty{} => {
                            
                        },
                        Maybe::NonEmpty{t, } => {
                            Hash::hash(t, _state)
                        },
                    }
                }
            }

            impl<T: DafnyType> AsRef<Maybe<T>>
                for Maybe<T> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8714,3)
            #[derive(Clone)]
            pub enum Suffixed<T: DafnyType, S: DafnyType> {
                Suffixed {
                    t: T,
                    suffix: Rc<crate::Std::JSON::Grammar::Maybe<Rc<crate::Std::JSON::Grammar::Structural<S>>>>
                }
            }

            impl<T: DafnyType, S: DafnyType> Suffixed<T, S> {
                /// Returns a borrow of the field t
                pub fn t(&self) -> &T {
                    match self {
                        Suffixed::Suffixed{t, suffix, } => t,
                    }
                }
                /// Returns a borrow of the field suffix
                pub fn suffix(&self) -> &Rc<crate::Std::JSON::Grammar::Maybe<Rc<crate::Std::JSON::Grammar::Structural<S>>>> {
                    match self {
                        Suffixed::Suffixed{t, suffix, } => suffix,
                    }
                }
            }

            impl<T: DafnyType, S: DafnyType> Debug
                for Suffixed<T, S> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<T: DafnyType, S: DafnyType> DafnyPrint
                for Suffixed<T, S> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        Suffixed::Suffixed{t, suffix, } => {
                            write!(_formatter, "Std.JSON.Grammar.Suffixed.Suffixed(")?;
                            DafnyPrint::fmt_print(t, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(suffix, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<T: DafnyType, S: DafnyType> Suffixed<T, S> {
                /// Given type parameter conversions, returns a lambda to convert this structure
                pub fn coerce<__T0: DafnyType, __T1: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(S) -> __T1 + 'static>) -> Rc<impl ::std::ops::Fn(Suffixed<T, S>) -> Suffixed<__T0, __T1>> {
                    Rc::new(move |this: Self| -> Suffixed<__T0, __T1>{
                            match this {
                                Suffixed::Suffixed{t, suffix, } => {
                                    Suffixed::Suffixed {
                                        t: f_0.clone()(t),
                                        suffix: rc_coerce(crate::Std::JSON::Grammar::Maybe::<Rc<crate::Std::JSON::Grammar::Structural<S>>>::coerce(rc_coerce(crate::Std::JSON::Grammar::Structural::<S>::coerce(f_1.clone()))))(suffix)
                                    }
                                },
                            }
                        })
                }
            }

            impl<T: DafnyType + Eq + Hash, S: DafnyType + Eq + Hash> PartialEq
                for Suffixed<T, S> {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (Suffixed::Suffixed{t, suffix, }, Suffixed::Suffixed{t: _2_t, suffix: _2_suffix, }) => {
                            t == _2_t && suffix == _2_suffix
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl<T: DafnyType + Eq + Hash, S: DafnyType + Eq + Hash> Eq
                for Suffixed<T, S> {}

            impl<T: DafnyType + Hash, S: DafnyType + Hash> Hash
                for Suffixed<T, S> {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        Suffixed::Suffixed{t, suffix, } => {
                            Hash::hash(t, _state);
                            Hash::hash(suffix, _state)
                        },
                    }
                }
            }

            impl<T: DafnyType, S: DafnyType> AsRef<Suffixed<T, S>>
                for Suffixed<T, S> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8716,3)
            pub type SuffixedSequence<D: DafnyType, S: DafnyType> = Sequence<Rc<crate::Std::JSON::Grammar::Suffixed<D, S>>>;

            /// DafnyStandardLibraries-rs.dfy(8719,3)
            #[derive(Clone)]
            pub enum Bracketed<L: DafnyType, D: DafnyType, S: DafnyType, R: DafnyType> {
                Bracketed {
                    l: Rc<crate::Std::JSON::Grammar::Structural<L>>,
                    data: crate::Std::JSON::Grammar::SuffixedSequence<D, S>,
                    r: Rc<crate::Std::JSON::Grammar::Structural<R>>
                }
            }

            impl<L: DafnyType, D: DafnyType, S: DafnyType, R: DafnyType> Bracketed<L, D, S, R> {
                /// Returns a borrow of the field l
                pub fn l(&self) -> &Rc<crate::Std::JSON::Grammar::Structural<L>> {
                    match self {
                        Bracketed::Bracketed{l, data, r, } => l,
                    }
                }
                /// Returns a borrow of the field data
                pub fn data(&self) -> &crate::Std::JSON::Grammar::SuffixedSequence<D, S> {
                    match self {
                        Bracketed::Bracketed{l, data, r, } => data,
                    }
                }
                /// Returns a borrow of the field r
                pub fn r(&self) -> &Rc<crate::Std::JSON::Grammar::Structural<R>> {
                    match self {
                        Bracketed::Bracketed{l, data, r, } => r,
                    }
                }
            }

            impl<L: DafnyType, D: DafnyType, S: DafnyType, R: DafnyType> Debug
                for Bracketed<L, D, S, R> {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl<L: DafnyType, D: DafnyType, S: DafnyType, R: DafnyType> DafnyPrint
                for Bracketed<L, D, S, R> {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        Bracketed::Bracketed{l, data, r, } => {
                            write!(_formatter, "Std.JSON.Grammar.Bracketed.Bracketed(")?;
                            DafnyPrint::fmt_print(l, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(data, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(r, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl<L: DafnyType, D: DafnyType, S: DafnyType, R: DafnyType> Bracketed<L, D, S, R> {
                /// Given type parameter conversions, returns a lambda to convert this structure
                pub fn coerce<__T0: DafnyType, __T1: DafnyType, __T2: DafnyType, __T3: DafnyType>(f_0: Rc<impl ::std::ops::Fn(L) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(D) -> __T1 + 'static>, f_2: Rc<impl ::std::ops::Fn(S) -> __T2 + 'static>, f_3: Rc<impl ::std::ops::Fn(R) -> __T3 + 'static>) -> Rc<impl ::std::ops::Fn(Bracketed<L, D, S, R>) -> Bracketed<__T0, __T1, __T2, __T3>> {
                    Rc::new(move |this: Self| -> Bracketed<__T0, __T1, __T2, __T3>{
                            match this {
                                Bracketed::Bracketed{l, data, r, } => {
                                    Bracketed::Bracketed {
                                        l: rc_coerce(crate::Std::JSON::Grammar::Structural::<L>::coerce(f_0.clone()))(l),
                                        data: upcast_id::<crate::Std::JSON::Grammar::SuffixedSequence<D, S>>()(data),
                                        r: rc_coerce(crate::Std::JSON::Grammar::Structural::<R>::coerce(f_3.clone()))(r)
                                    }
                                },
                            }
                        })
                }
            }

            impl<L: DafnyType + Eq + Hash, D: DafnyType + Eq + Hash, S: DafnyType + Eq + Hash, R: DafnyType + Eq + Hash> PartialEq
                for Bracketed<L, D, S, R> {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (Bracketed::Bracketed{l, data, r, }, Bracketed::Bracketed{l: _2_l, data: _2_data, r: _2_r, }) => {
                            l == _2_l && data == _2_data && r == _2_r
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl<L: DafnyType + Eq + Hash, D: DafnyType + Eq + Hash, S: DafnyType + Eq + Hash, R: DafnyType + Eq + Hash> Eq
                for Bracketed<L, D, S, R> {}

            impl<L: DafnyType + Hash, D: DafnyType + Hash, S: DafnyType + Hash, R: DafnyType + Hash> Hash
                for Bracketed<L, D, S, R> {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        Bracketed::Bracketed{l, data, r, } => {
                            Hash::hash(l, _state);
                            Hash::hash(data, _state);
                            Hash::hash(r, _state)
                        },
                    }
                }
            }

            impl<L: DafnyType, D: DafnyType, S: DafnyType, R: DafnyType> AsRef<Bracketed<L, D, S, R>>
                for Bracketed<L, D, S, R> {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8721,3)
            pub type jnull = Rc<View_>;

            /// An element of jnull
            pub fn __init_jnull() -> Rc<View_> {
                View_::OfBytes(&crate::Std::JSON::Grammar::_default::NULL())
            }

            /// DafnyStandardLibraries-rs.dfy(8725,3)
            pub type jbool = Rc<View_>;

            /// An element of jbool
            pub fn __init_jbool() -> Rc<View_> {
                View_::OfBytes(&crate::Std::JSON::Grammar::_default::TRUE())
            }

            /// DafnyStandardLibraries-rs.dfy(8729,3)
            pub type jdigits = Rc<View_>;

            /// An element of jdigits
            pub fn __init_jdigits() -> Rc<View_> {
                View_::OfBytes(&(seq![] as Sequence<u8>))
            }

            /// DafnyStandardLibraries-rs.dfy(8733,3)
            pub type jnum = Rc<View_>;

            /// An element of jnum
            pub fn __init_jnum() -> Rc<View_> {
                View_::OfBytes(&seq![DafnyChar(char::from_u32(48).unwrap()).0 as u8])
            }

            /// DafnyStandardLibraries-rs.dfy(8737,3)
            pub type jint = Rc<View_>;

            /// An element of jint
            pub fn __init_jint() -> Rc<View_> {
                View_::OfBytes(&seq![DafnyChar(char::from_u32(48).unwrap()).0 as u8])
            }

            /// DafnyStandardLibraries-rs.dfy(8741,3)
            pub type jstr = Rc<View_>;

            /// An element of jstr
            pub fn __init_jstr() -> Rc<View_> {
                View_::OfBytes(&(seq![] as Sequence<u8>))
            }

            /// DafnyStandardLibraries-rs.dfy(8745,3)
            #[derive(Clone)]
            pub enum jstring {
                JString {
                    lq: crate::Std::JSON::Grammar::jquote,
                    contents: crate::Std::JSON::Grammar::jstr,
                    rq: crate::Std::JSON::Grammar::jquote
                }
            }

            impl jstring {
                /// Returns a borrow of the field lq
                pub fn lq(&self) -> &crate::Std::JSON::Grammar::jquote {
                    match self {
                        jstring::JString{lq, contents, rq, } => lq,
                    }
                }
                /// Returns a borrow of the field contents
                pub fn contents(&self) -> &crate::Std::JSON::Grammar::jstr {
                    match self {
                        jstring::JString{lq, contents, rq, } => contents,
                    }
                }
                /// Returns a borrow of the field rq
                pub fn rq(&self) -> &crate::Std::JSON::Grammar::jquote {
                    match self {
                        jstring::JString{lq, contents, rq, } => rq,
                    }
                }
            }

            impl Debug
                for jstring {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for jstring {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        jstring::JString{lq, contents, rq, } => {
                            write!(_formatter, "Std.JSON.Grammar.jstring.JString(")?;
                            DafnyPrint::fmt_print(lq, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(contents, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(rq, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for jstring {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (jstring::JString{lq, contents, rq, }, jstring::JString{lq: _2_lq, contents: _2_contents, rq: _2_rq, }) => {
                            lq == _2_lq && contents == _2_contents && rq == _2_rq
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for jstring {}

            impl Hash
                for jstring {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        jstring::JString{lq, contents, rq, } => {
                            Hash::hash(lq, _state);
                            Hash::hash(contents, _state);
                            Hash::hash(rq, _state)
                        },
                    }
                }
            }

            impl AsRef<jstring>
                for jstring {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8747,3)
            #[derive(Clone)]
            pub enum jKeyValue {
                KeyValue {
                    k: Rc<crate::Std::JSON::Grammar::jstring>,
                    colon: Rc<crate::Std::JSON::Grammar::Structural<crate::Std::JSON::Grammar::jcolon>>,
                    v: Rc<crate::Std::JSON::Grammar::Value>
                }
            }

            impl jKeyValue {
                /// Returns a borrow of the field k
                pub fn k(&self) -> &Rc<crate::Std::JSON::Grammar::jstring> {
                    match self {
                        jKeyValue::KeyValue{k, colon, v, } => k,
                    }
                }
                /// Returns a borrow of the field colon
                pub fn colon(&self) -> &Rc<crate::Std::JSON::Grammar::Structural<crate::Std::JSON::Grammar::jcolon>> {
                    match self {
                        jKeyValue::KeyValue{k, colon, v, } => colon,
                    }
                }
                /// Returns a borrow of the field v
                pub fn v(&self) -> &Rc<crate::Std::JSON::Grammar::Value> {
                    match self {
                        jKeyValue::KeyValue{k, colon, v, } => v,
                    }
                }
            }

            impl Debug
                for jKeyValue {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for jKeyValue {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        jKeyValue::KeyValue{k, colon, v, } => {
                            write!(_formatter, "Std.JSON.Grammar.jKeyValue.KeyValue(")?;
                            DafnyPrint::fmt_print(k, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(colon, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(v, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for jKeyValue {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (jKeyValue::KeyValue{k, colon, v, }, jKeyValue::KeyValue{k: _2_k, colon: _2_colon, v: _2_v, }) => {
                            k == _2_k && colon == _2_colon && v == _2_v
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for jKeyValue {}

            impl Hash
                for jKeyValue {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        jKeyValue::KeyValue{k, colon, v, } => {
                            Hash::hash(k, _state);
                            Hash::hash(colon, _state);
                            Hash::hash(v, _state)
                        },
                    }
                }
            }

            impl AsRef<jKeyValue>
                for jKeyValue {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8761,3)
            #[derive(Clone)]
            pub enum jfrac {
                JFrac {
                    period: crate::Std::JSON::Grammar::jperiod,
                    num: crate::Std::JSON::Grammar::jnum
                }
            }

            impl jfrac {
                /// Returns a borrow of the field period
                pub fn period(&self) -> &crate::Std::JSON::Grammar::jperiod {
                    match self {
                        jfrac::JFrac{period, num, } => period,
                    }
                }
                /// Returns a borrow of the field num
                pub fn num(&self) -> &crate::Std::JSON::Grammar::jnum {
                    match self {
                        jfrac::JFrac{period, num, } => num,
                    }
                }
            }

            impl Debug
                for jfrac {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for jfrac {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        jfrac::JFrac{period, num, } => {
                            write!(_formatter, "Std.JSON.Grammar.jfrac.JFrac(")?;
                            DafnyPrint::fmt_print(period, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(num, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for jfrac {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (jfrac::JFrac{period, num, }, jfrac::JFrac{period: _2_period, num: _2_num, }) => {
                            period == _2_period && num == _2_num
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for jfrac {}

            impl Hash
                for jfrac {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        jfrac::JFrac{period, num, } => {
                            Hash::hash(period, _state);
                            Hash::hash(num, _state)
                        },
                    }
                }
            }

            impl AsRef<jfrac>
                for jfrac {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8763,3)
            #[derive(Clone)]
            pub enum jexp {
                JExp {
                    e: crate::Std::JSON::Grammar::je,
                    sign: crate::Std::JSON::Grammar::jsign,
                    num: crate::Std::JSON::Grammar::jnum
                }
            }

            impl jexp {
                /// Returns a borrow of the field e
                pub fn e(&self) -> &crate::Std::JSON::Grammar::je {
                    match self {
                        jexp::JExp{e, sign, num, } => e,
                    }
                }
                /// Returns a borrow of the field sign
                pub fn sign(&self) -> &crate::Std::JSON::Grammar::jsign {
                    match self {
                        jexp::JExp{e, sign, num, } => sign,
                    }
                }
                /// Returns a borrow of the field num
                pub fn num(&self) -> &crate::Std::JSON::Grammar::jnum {
                    match self {
                        jexp::JExp{e, sign, num, } => num,
                    }
                }
            }

            impl Debug
                for jexp {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for jexp {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        jexp::JExp{e, sign, num, } => {
                            write!(_formatter, "Std.JSON.Grammar.jexp.JExp(")?;
                            DafnyPrint::fmt_print(e, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(sign, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(num, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for jexp {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (jexp::JExp{e, sign, num, }, jexp::JExp{e: _2_e, sign: _2_sign, num: _2_num, }) => {
                            e == _2_e && sign == _2_sign && num == _2_num
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for jexp {}

            impl Hash
                for jexp {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        jexp::JExp{e, sign, num, } => {
                            Hash::hash(e, _state);
                            Hash::hash(sign, _state);
                            Hash::hash(num, _state)
                        },
                    }
                }
            }

            impl AsRef<jexp>
                for jexp {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8765,3)
            #[derive(Clone)]
            pub enum jnumber {
                JNumber {
                    minus: crate::Std::JSON::Grammar::jminus,
                    num: crate::Std::JSON::Grammar::jnum,
                    frac: Rc<crate::Std::JSON::Grammar::Maybe<Rc<crate::Std::JSON::Grammar::jfrac>>>,
                    exp: Rc<crate::Std::JSON::Grammar::Maybe<Rc<crate::Std::JSON::Grammar::jexp>>>
                }
            }

            impl jnumber {
                /// Returns a borrow of the field minus
                pub fn minus(&self) -> &crate::Std::JSON::Grammar::jminus {
                    match self {
                        jnumber::JNumber{minus, num, frac, exp, } => minus,
                    }
                }
                /// Returns a borrow of the field num
                pub fn num(&self) -> &crate::Std::JSON::Grammar::jnum {
                    match self {
                        jnumber::JNumber{minus, num, frac, exp, } => num,
                    }
                }
                /// Returns a borrow of the field frac
                pub fn frac(&self) -> &Rc<crate::Std::JSON::Grammar::Maybe<Rc<crate::Std::JSON::Grammar::jfrac>>> {
                    match self {
                        jnumber::JNumber{minus, num, frac, exp, } => frac,
                    }
                }
                /// Returns a borrow of the field exp
                pub fn exp(&self) -> &Rc<crate::Std::JSON::Grammar::Maybe<Rc<crate::Std::JSON::Grammar::jexp>>> {
                    match self {
                        jnumber::JNumber{minus, num, frac, exp, } => exp,
                    }
                }
            }

            impl Debug
                for jnumber {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for jnumber {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        jnumber::JNumber{minus, num, frac, exp, } => {
                            write!(_formatter, "Std.JSON.Grammar.jnumber.JNumber(")?;
                            DafnyPrint::fmt_print(minus, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(num, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(frac, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(exp, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for jnumber {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (jnumber::JNumber{minus, num, frac, exp, }, jnumber::JNumber{minus: _2_minus, num: _2_num, frac: _2_frac, exp: _2_exp, }) => {
                            minus == _2_minus && num == _2_num && frac == _2_frac && exp == _2_exp
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for jnumber {}

            impl Hash
                for jnumber {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        jnumber::JNumber{minus, num, frac, exp, } => {
                            Hash::hash(minus, _state);
                            Hash::hash(num, _state);
                            Hash::hash(frac, _state);
                            Hash::hash(exp, _state)
                        },
                    }
                }
            }

            impl AsRef<jnumber>
                for jnumber {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8767,3)
            #[derive(Clone)]
            pub enum Value {
                Null {
                    n: crate::Std::JSON::Grammar::jnull
                },
                Bool {
                    b: crate::Std::JSON::Grammar::jbool
                },
                String {
                    str: Rc<crate::Std::JSON::Grammar::jstring>
                },
                Number {
                    num: Rc<crate::Std::JSON::Grammar::jnumber>
                },
                Object {
                    obj: Rc<crate::Std::JSON::Grammar::Bracketed<crate::Std::JSON::Grammar::jlbrace, Rc<crate::Std::JSON::Grammar::jKeyValue>, crate::Std::JSON::Grammar::jcomma, crate::Std::JSON::Grammar::jrbrace>>
                },
                Array {
                    arr: Rc<crate::Std::JSON::Grammar::Bracketed<crate::Std::JSON::Grammar::jlbracket, Rc<crate::Std::JSON::Grammar::Value>, crate::Std::JSON::Grammar::jcomma, crate::Std::JSON::Grammar::jrbracket>>
                }
            }

            impl Value {
                /// Gets the field n for all enum members which have it
                pub fn n(&self) -> &crate::Std::JSON::Grammar::jnull {
                    match self {
                        Value::Null{n, } => n,
                        Value::Bool{b, } => panic!("field does not exist on this variant"),
                        Value::String{str, } => panic!("field does not exist on this variant"),
                        Value::Number{num, } => panic!("field does not exist on this variant"),
                        Value::Object{obj, } => panic!("field does not exist on this variant"),
                        Value::Array{arr, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field b for all enum members which have it
                pub fn b(&self) -> &crate::Std::JSON::Grammar::jbool {
                    match self {
                        Value::Null{n, } => panic!("field does not exist on this variant"),
                        Value::Bool{b, } => b,
                        Value::String{str, } => panic!("field does not exist on this variant"),
                        Value::Number{num, } => panic!("field does not exist on this variant"),
                        Value::Object{obj, } => panic!("field does not exist on this variant"),
                        Value::Array{arr, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field str for all enum members which have it
                pub fn str(&self) -> &Rc<crate::Std::JSON::Grammar::jstring> {
                    match self {
                        Value::Null{n, } => panic!("field does not exist on this variant"),
                        Value::Bool{b, } => panic!("field does not exist on this variant"),
                        Value::String{str, } => str,
                        Value::Number{num, } => panic!("field does not exist on this variant"),
                        Value::Object{obj, } => panic!("field does not exist on this variant"),
                        Value::Array{arr, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field num for all enum members which have it
                pub fn num(&self) -> &Rc<crate::Std::JSON::Grammar::jnumber> {
                    match self {
                        Value::Null{n, } => panic!("field does not exist on this variant"),
                        Value::Bool{b, } => panic!("field does not exist on this variant"),
                        Value::String{str, } => panic!("field does not exist on this variant"),
                        Value::Number{num, } => num,
                        Value::Object{obj, } => panic!("field does not exist on this variant"),
                        Value::Array{arr, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field obj for all enum members which have it
                pub fn obj(&self) -> &Rc<crate::Std::JSON::Grammar::Bracketed<crate::Std::JSON::Grammar::jlbrace, Rc<crate::Std::JSON::Grammar::jKeyValue>, crate::Std::JSON::Grammar::jcomma, crate::Std::JSON::Grammar::jrbrace>> {
                    match self {
                        Value::Null{n, } => panic!("field does not exist on this variant"),
                        Value::Bool{b, } => panic!("field does not exist on this variant"),
                        Value::String{str, } => panic!("field does not exist on this variant"),
                        Value::Number{num, } => panic!("field does not exist on this variant"),
                        Value::Object{obj, } => obj,
                        Value::Array{arr, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field arr for all enum members which have it
                pub fn arr(&self) -> &Rc<crate::Std::JSON::Grammar::Bracketed<crate::Std::JSON::Grammar::jlbracket, Rc<crate::Std::JSON::Grammar::Value>, crate::Std::JSON::Grammar::jcomma, crate::Std::JSON::Grammar::jrbracket>> {
                    match self {
                        Value::Null{n, } => panic!("field does not exist on this variant"),
                        Value::Bool{b, } => panic!("field does not exist on this variant"),
                        Value::String{str, } => panic!("field does not exist on this variant"),
                        Value::Number{num, } => panic!("field does not exist on this variant"),
                        Value::Object{obj, } => panic!("field does not exist on this variant"),
                        Value::Array{arr, } => arr,
                    }
                }
            }

            impl Debug
                for Value {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for Value {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        Value::Null{n, } => {
                            write!(_formatter, "Std.JSON.Grammar.Value.Null(")?;
                            DafnyPrint::fmt_print(n, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        Value::Bool{b, } => {
                            write!(_formatter, "Std.JSON.Grammar.Value.Bool(")?;
                            DafnyPrint::fmt_print(b, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        Value::String{str, } => {
                            write!(_formatter, "Std.JSON.Grammar.Value.String(")?;
                            DafnyPrint::fmt_print(str, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        Value::Number{num, } => {
                            write!(_formatter, "Std.JSON.Grammar.Value.Number(")?;
                            DafnyPrint::fmt_print(num, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        Value::Object{obj, } => {
                            write!(_formatter, "Std.JSON.Grammar.Value.Object(")?;
                            DafnyPrint::fmt_print(obj, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        Value::Array{arr, } => {
                            write!(_formatter, "Std.JSON.Grammar.Value.Array(")?;
                            DafnyPrint::fmt_print(arr, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for Value {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (Value::Null{n, }, Value::Null{n: _2_n, }) => {
                            n == _2_n
                        },
                        (Value::Bool{b, }, Value::Bool{b: _2_b, }) => {
                            b == _2_b
                        },
                        (Value::String{str, }, Value::String{str: _2_str, }) => {
                            str == _2_str
                        },
                        (Value::Number{num, }, Value::Number{num: _2_num, }) => {
                            num == _2_num
                        },
                        (Value::Object{obj, }, Value::Object{obj: _2_obj, }) => {
                            obj == _2_obj
                        },
                        (Value::Array{arr, }, Value::Array{arr: _2_arr, }) => {
                            arr == _2_arr
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for Value {}

            impl Hash
                for Value {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        Value::Null{n, } => {
                            Hash::hash(n, _state)
                        },
                        Value::Bool{b, } => {
                            Hash::hash(b, _state)
                        },
                        Value::String{str, } => {
                            Hash::hash(str, _state)
                        },
                        Value::Number{num, } => {
                            Hash::hash(num, _state)
                        },
                        Value::Object{obj, } => {
                            Hash::hash(obj, _state)
                        },
                        Value::Array{arr, } => {
                            Hash::hash(arr, _state)
                        },
                    }
                }
            }

            impl AsRef<Value>
                for Value {
                fn as_ref(&self) -> &Self {
                    self
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(8772,1)
        pub mod Serializer {
            pub use crate::Std::JSON::Grammar::jbool;
            pub use crate::Std::JSON::Utils::Views::Core::View_;
            pub use ::dafny_runtime::DafnyType;
            pub use ::dafny_runtime::Sequence;
            pub use ::std::rc::Rc;
            pub use crate::Std::JSON::Errors::SerializationError;
            pub use crate::Std::Wrappers::Outcome;
            pub use ::dafny_runtime::DafnyChar;
            pub use crate::Std::Wrappers::Result;
            pub use crate::Std::JSON::Grammar::jstring;
            pub use ::dafny_runtime::int;
            pub use crate::Std::Wrappers::Outcome::Pass;
            pub use ::dafny_runtime::DafnyInt;
            pub use crate::Std::JSON::Grammar::jminus;
            pub use ::dafny_runtime::seq;
            pub use ::std::primitive::char;
            pub use crate::Std::JSON::Utils::Views::Core::View;
            pub use crate::Std::JSON::Values::Decimal;
            pub use crate::Std::JSON::Grammar::jnumber;
            pub use crate::Std::JSON::Grammar::jnum;
            pub use crate::Std::JSON::Grammar::Maybe;
            pub use crate::Std::JSON::Grammar::jfrac;
            pub use crate::Std::JSON::Grammar::jexp;
            pub use crate::Std::JSON::Grammar::je;
            pub use crate::Std::JSON::Grammar::jsign;
            pub use crate::Std::JSON::Grammar::Structural;
            pub use crate::Std::JSON::Values::JSON;
            pub use crate::Std::JSON::Grammar::jKeyValue;
            pub use crate::Std::JSON::Grammar::Value;
            pub use ::dafny_runtime::_System::nat;
            pub use crate::Std::JSON::Grammar::SuffixedSequence;
            pub use crate::Std::JSON::Grammar::Suffixed;
            pub use crate::Std::JSON::Grammar::Bracketed;
            pub use crate::Std::JSON::Grammar::jlbrace;
            pub use crate::Std::JSON::Grammar::jcomma;
            pub use crate::Std::JSON::Grammar::jrbrace;
            pub use crate::Std::JSON::Grammar::jlbracket;
            pub use crate::Std::JSON::Grammar::jrbracket;
            pub use crate::Std::JSON::Values::JSON::Null;
            pub use crate::Std::JSON::Values::JSON::Bool;
            pub use crate::Std::JSON::Values::JSON::String;
            pub use crate::Std::JSON::Values::JSON::Number;
            pub use crate::Std::JSON::Values::JSON::Object;
            pub use crate::Std::JSON::ByteStrConversion::CharSeq;
            pub use crate::Std::JSON::Grammar::jcolon;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(8773,3)
                pub fn Bool(b: bool) -> jbool {
                    View_::OfBytes(&(if b {
                            crate::Std::JSON::Grammar::_default::TRUE()
                        } else {
                            crate::Std::JSON::Grammar::_default::FALSE()
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(8778,3)
                pub fn CheckLength<_T: DafnyType>(s: &Sequence<_T>, err: &Rc<SerializationError>) -> Rc<Outcome<Rc<SerializationError>>> {
                    Outcome::<Rc<SerializationError>>::Need(s.cardinality() < crate::Std::BoundedInts::_default::TWO_TO_THE_32(), err)
                }
                /// DafnyStandardLibraries-rs.dfy(8783,3)
                pub fn String(str: &Sequence<DafnyChar>) -> Rc<Result<Rc<jstring>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<u8>, Rc<SerializationError>>> = crate::Std::JSON::Spec::_default::EscapeToUTF8(str, &int!(0));
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Rc<jstring>>()
                    } else {
                        let mut bs: Sequence<u8> = valueOrError0.Extract();
                        let mut o: Rc<Outcome<Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::CheckLength::<u8>(&bs, &Rc::new(SerializationError::StringTooLong {
                                        s: str.clone()
                                    }));
                        if matches!((&o).as_ref(), Pass{ .. }) {
                            Rc::new(Result::Success::<Rc<jstring>, Rc<SerializationError>> {
                                    value: Rc::new(jstring::JString {
                                                lq: crate::Std::JSON::Grammar::_default::DOUBLEQUOTE(),
                                                contents: View_::OfBytes(&bs),
                                                rq: crate::Std::JSON::Grammar::_default::DOUBLEQUOTE()
                                            })
                                })
                        } else {
                            Rc::new(Result::Failure::<Rc<jstring>, Rc<SerializationError>> {
                                    error: o.error().clone()
                                })
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8788,3)
                pub fn Sign(n: &DafnyInt) -> jminus {
                    View_::OfBytes(&(if n.clone() < int!(0) {
                            seq![DafnyChar(char::from_u32(45).unwrap()).0 as u8]
                        } else {
                            seq![] as Sequence<u8>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(8796,3)
                pub fn _Int_k(n: &DafnyInt) -> Sequence<u8> {
                    crate::Std::JSON::ByteStrConversion::_default::OfInt(n, crate::Std::JSON::Serializer::_default::MINUS())
                }
                /// DafnyStandardLibraries-rs.dfy(8802,3)
                pub fn Int(n: &DafnyInt) -> Rc<Result<View, Rc<SerializationError>>> {
                    let mut bs: Sequence<u8> = crate::Std::JSON::Serializer::_default::_Int_k(n);
                    let mut o: Rc<Outcome<Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::CheckLength::<u8>(&bs, &Rc::new(SerializationError::IntTooLarge {
                                    i: n.clone()
                                }));
                    if matches!((&o).as_ref(), Pass{ .. }) {
                        Rc::new(Result::Success::<View, Rc<SerializationError>> {
                                value: View_::OfBytes(&bs)
                            })
                    } else {
                        Rc::new(Result::Failure::<View, Rc<SerializationError>> {
                                error: o.error().clone()
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8812,3)
                pub fn Number(dec: &Rc<Decimal>) -> Rc<Result<Rc<jnumber>, Rc<SerializationError>>> {
                    let mut minus: jminus = crate::Std::JSON::Serializer::_default::Sign(dec.n());
                    let mut valueOrError0: Rc<Result<View, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::Int(&crate::Std::Math::_default::Abs(dec.n()));
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Rc<jnumber>>()
                    } else {
                        let mut num: jnum = valueOrError0.Extract();
                        let mut frac: Rc<Maybe<Rc<jfrac>>> = Rc::new(Maybe::Empty::<Rc<jfrac>> {});
                        let mut valueOrError1: Rc<Result<Rc<Maybe<Rc<jexp>>>, Rc<SerializationError>>> = if dec.e10().clone() == int!(0) {
                                Rc::new(Result::Success::<Rc<Maybe<Rc<jexp>>>, Rc<SerializationError>> {
                                        value: Rc::new(Maybe::Empty::<Rc<jexp>> {})
                                    })
                            } else {
                                {
                                    let __pat_let1_0: View = View_::OfBytes(&seq![DafnyChar(char::from_u32(101).unwrap()).0 as u8]);
                                    {
                                        let e: je = __pat_let1_0.clone();
                                        {
                                            let __pat_let2_0: jminus = crate::Std::JSON::Serializer::_default::Sign(dec.e10());
                                            {
                                                let sign: jsign = __pat_let2_0.clone();
                                                {
                                                    let __pat_let3_0: Rc<Result<View, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::Int(&crate::Std::Math::_default::Abs(dec.e10()));
                                                    {
                                                        let valueOrError2: Rc<Result<View, Rc<SerializationError>>> = __pat_let3_0.clone();
                                                        if valueOrError2.IsFailure() {
                                                            valueOrError2.PropagateFailure::<Rc<Maybe<Rc<jexp>>>>()
                                                        } else {
                                                            {
                                                                let __pat_let4_0: View = valueOrError2.Extract();
                                                                {
                                                                    let num: jnum = __pat_let4_0.clone();
                                                                    Rc::new(Result::Success::<Rc<Maybe<Rc<jexp>>>, Rc<SerializationError>> {
                                                                            value: Rc::new(Maybe::NonEmpty::<Rc<jexp>> {
                                                                                        t: Rc::new(jexp::JExp {
                                                                                                    e: e.clone(),
                                                                                                    sign: sign.clone(),
                                                                                                    num: num.clone()
                                                                                                })
                                                                                    })
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
                            };
                        if valueOrError1.IsFailure() {
                            valueOrError1.PropagateFailure::<Rc<jnumber>>()
                        } else {
                            let mut exp: Rc<Maybe<Rc<jexp>>> = valueOrError1.Extract();
                            Rc::new(Result::Success::<Rc<jnumber>, Rc<SerializationError>> {
                                    value: Rc::new(jnumber::JNumber {
                                                minus: minus.clone(),
                                                num: num.clone(),
                                                frac: Rc::new(Maybe::Empty::<Rc<jfrac>> {}),
                                                exp: exp.clone()
                                            })
                                })
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8818,3)
                pub fn MkStructural<_T: DafnyType>(v: &_T) -> Rc<Structural<_T>> {
                    Rc::new(Structural::Structural::<_T> {
                            before: crate::Std::JSON::Grammar::_default::EMPTY(),
                            t: v.clone(),
                            after: crate::Std::JSON::Grammar::_default::EMPTY()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8825,3)
                pub fn KeyValue(kv: &(Sequence<DafnyChar>, Rc<JSON>)) -> Rc<Result<Rc<jKeyValue>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Rc<jstring>, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::String(&kv.0.clone());
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Rc<jKeyValue>>()
                    } else {
                        let mut k: Rc<jstring> = valueOrError0.Extract();
                        let mut valueOrError1: Rc<Result<Rc<Value>, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::Value(&kv.1.clone());
                        if valueOrError1.IsFailure() {
                            valueOrError1.PropagateFailure::<Rc<jKeyValue>>()
                        } else {
                            let mut v: Rc<Value> = valueOrError1.Extract();
                            Rc::new(Result::Success::<Rc<jKeyValue>, Rc<SerializationError>> {
                                    value: Rc::new(jKeyValue::KeyValue {
                                                k: k.clone(),
                                                colon: crate::Std::JSON::Serializer::_default::COLON(),
                                                v: v.clone()
                                            })
                                })
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8830,3)
                pub fn MkSuffixedSequence<_D: DafnyType, _S: DafnyType>(ds: &Sequence<_D>, suffix: &Rc<Structural<_S>>, start: &nat) -> SuffixedSequence<_D, _S> {
                    let mut _accumulator: SuffixedSequence<_D, _S> = seq![] as Sequence<Rc<Suffixed<_D, _S>>>;
                    let mut _r0 = ds.clone();
                    let mut _r1 = suffix.clone();
                    let mut _r2 = start.clone();
                    'TAIL_CALL_START: loop {
                        let ds = _r0;
                        let suffix = _r1;
                        let start = _r2;
                        if !(start.clone() < ds.cardinality()) {
                            return _accumulator.concat(&(seq![] as Sequence<Rc<Suffixed<_D, _S>>>));
                        } else {
                            if start.clone() == ds.cardinality() - int!(1) {
                                return _accumulator.concat(&seq![Rc::new(Suffixed::Suffixed::<_D, _S> {
                                                    t: ds.get(&start),
                                                    suffix: Rc::new(Maybe::Empty::<Rc<Structural<_S>>> {})
                                                })]);
                            } else {
                                _accumulator = _accumulator.concat(&seq![Rc::new(Suffixed::Suffixed::<_D, _S> {
                                                    t: ds.get(&start),
                                                    suffix: Rc::new(Maybe::NonEmpty::<Rc<Structural<_S>>> {
                                                                t: suffix.clone()
                                                            })
                                                })]);
                                let mut _in0: Sequence<_D> = ds.clone();
                                let mut _in1: Rc<Structural<_S>> = suffix.clone();
                                let mut _in2: DafnyInt = start.clone() + int!(1);
                                _r0 = _in0.clone();
                                _r1 = _in1.clone();
                                _r2 = _in2.clone();
                                continue 'TAIL_CALL_START;
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8843,3)
                pub fn Object(obj: &Sequence<(Sequence<DafnyChar>, Rc<JSON>)>) -> Rc<Result<Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<Rc<jKeyValue>>, Rc<SerializationError>>> = crate::Std::Collections::Seq::_default::MapWithResult::<(Sequence<DafnyChar>, Rc<JSON>), Rc<jKeyValue>, Rc<SerializationError>>({
                                let obj: Sequence<(Sequence<DafnyChar>, Rc<JSON>)> = obj.clone();
                                &({
                                    Rc::new(move |v: &(Sequence<DafnyChar>, Rc<JSON>)| -> Rc<Result<Rc<jKeyValue>, Rc<SerializationError>>>{
            crate::Std::JSON::Serializer::_default::KeyValue(v)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                })
                            }, obj);
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Rc<Bracketed<View, Rc<jKeyValue>, jcomma, View>>>()
                    } else {
                        let mut items: Sequence<Rc<jKeyValue>> = valueOrError0.Extract();
                        Rc::new(Result::Success::<Rc<Bracketed<View, Rc<jKeyValue>, jcomma, View>>, Rc<SerializationError>> {
                                value: Rc::new(Bracketed::Bracketed::<View, Rc<jKeyValue>, jcomma, View> {
                                            l: crate::Std::JSON::Serializer::_default::MkStructural::<View>(&crate::Std::JSON::Grammar::_default::LBRACE()),
                                            data: crate::Std::JSON::Serializer::_default::MkSuffixedSequence::<Rc<jKeyValue>, jcomma>(&items, &crate::Std::JSON::Serializer::_default::COMMA(), &int!(0)),
                                            r: crate::Std::JSON::Serializer::_default::MkStructural::<View>(&crate::Std::JSON::Grammar::_default::RBRACE())
                                        })
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8848,3)
                pub fn Array(arr: &Sequence<Rc<JSON>>) -> Rc<Result<Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<Rc<Value>>, Rc<SerializationError>>> = crate::Std::Collections::Seq::_default::MapWithResult::<Rc<JSON>, Rc<Value>, Rc<SerializationError>>({
                                let arr: Sequence<Rc<JSON>> = arr.clone();
                                &({
                                    Rc::new(move |v: &Rc<JSON>| -> Rc<Result<Rc<Value>, Rc<SerializationError>>>{
            crate::Std::JSON::Serializer::_default::Value(v)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                })
                            }, arr);
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Rc<Bracketed<View, Rc<Value>, jcomma, View>>>()
                    } else {
                        let mut items: Sequence<Rc<Value>> = valueOrError0.Extract();
                        Rc::new(Result::Success::<Rc<Bracketed<View, Rc<Value>, jcomma, View>>, Rc<SerializationError>> {
                                value: Rc::new(Bracketed::Bracketed::<View, Rc<Value>, jcomma, View> {
                                            l: crate::Std::JSON::Serializer::_default::MkStructural::<View>(&crate::Std::JSON::Grammar::_default::LBRACKET()),
                                            data: crate::Std::JSON::Serializer::_default::MkSuffixedSequence::<Rc<Value>, jcomma>(&items, &crate::Std::JSON::Serializer::_default::COMMA(), &int!(0)),
                                            r: crate::Std::JSON::Serializer::_default::MkStructural::<View>(&crate::Std::JSON::Grammar::_default::RBRACKET())
                                        })
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8853,3)
                pub fn Value(js: &Rc<JSON>) -> Rc<Result<Rc<Value>, Rc<SerializationError>>> {
                    let mut _source0: Rc<JSON> = js.clone();
                    if matches!((&_source0).as_ref(), Null{ .. }) {
                        Rc::new(Result::Success::<Rc<Value>, Rc<SerializationError>> {
                                value: Rc::new(Value::Null {
                                            n: View_::OfBytes(&crate::Std::JSON::Grammar::_default::NULL())
                                        })
                            })
                    } else {
                        if matches!((&_source0).as_ref(), Bool{ .. }) {
                            let mut ___mcc_h0: bool = _source0.b().clone();
                            let mut b: bool = ___mcc_h0;
                            Rc::new(Result::Success::<Rc<Value>, Rc<SerializationError>> {
                                    value: Rc::new(Value::Bool {
                                                b: crate::Std::JSON::Serializer::_default::Bool(b)
                                            })
                                })
                        } else {
                            if matches!((&_source0).as_ref(), String{ .. }) {
                                let mut ___mcc_h1: Sequence<DafnyChar> = _source0.str().clone();
                                let mut str: Sequence<DafnyChar> = ___mcc_h1.clone();
                                let mut valueOrError0: Rc<Result<Rc<jstring>, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::String(&str);
                                if valueOrError0.IsFailure() {
                                    valueOrError0.PropagateFailure::<Rc<Value>>()
                                } else {
                                    let mut s: Rc<jstring> = valueOrError0.Extract();
                                    Rc::new(Result::Success::<Rc<Value>, Rc<SerializationError>> {
                                            value: Rc::new(Value::String {
                                                        str: s.clone()
                                                    })
                                        })
                                }
                            } else {
                                if matches!((&_source0).as_ref(), Number{ .. }) {
                                    let mut ___mcc_h2: Rc<Decimal> = _source0.num().clone();
                                    let mut dec: Rc<Decimal> = ___mcc_h2.clone();
                                    let mut valueOrError1: Rc<Result<Rc<jnumber>, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::Number(&dec);
                                    if valueOrError1.IsFailure() {
                                        valueOrError1.PropagateFailure::<Rc<Value>>()
                                    } else {
                                        let mut n: Rc<jnumber> = valueOrError1.Extract();
                                        Rc::new(Result::Success::<Rc<Value>, Rc<SerializationError>> {
                                                value: Rc::new(Value::Number {
                                                            num: n.clone()
                                                        })
                                            })
                                    }
                                } else {
                                    if matches!((&_source0).as_ref(), Object{ .. }) {
                                        let mut ___mcc_h3: Sequence<(Sequence<DafnyChar>, Rc<JSON>)> = _source0.obj().clone();
                                        let mut obj: Sequence<(Sequence<DafnyChar>, Rc<JSON>)> = ___mcc_h3.clone();
                                        let mut valueOrError2: Rc<Result<Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::Object(&obj);
                                        if valueOrError2.IsFailure() {
                                            valueOrError2.PropagateFailure::<Rc<Value>>()
                                        } else {
                                            let mut o: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = valueOrError2.Extract();
                                            Rc::new(Result::Success::<Rc<Value>, Rc<SerializationError>> {
                                                    value: Rc::new(Value::Object {
                                                                obj: o.clone()
                                                            })
                                                })
                                        }
                                    } else {
                                        let mut ___mcc_h4: Sequence<Rc<JSON>> = _source0.arr().clone();
                                        let mut arr: Sequence<Rc<JSON>> = ___mcc_h4.clone();
                                        let mut valueOrError3: Rc<Result<Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::Array(&arr);
                                        if valueOrError3.IsFailure() {
                                            valueOrError3.PropagateFailure::<Rc<Value>>()
                                        } else {
                                            let mut a: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = valueOrError3.Extract();
                                            Rc::new(Result::Success::<Rc<Value>, Rc<SerializationError>> {
                                                    value: Rc::new(Value::Array {
                                                                arr: a.clone()
                                                            })
                                                })
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8870,3)
                pub fn JSON(js: &Rc<JSON>) -> Rc<Result<Rc<Structural<Rc<Value>>>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Rc<Value>, Rc<SerializationError>>> = crate::Std::JSON::Serializer::_default::Value(js);
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Rc<Structural<Rc<Value>>>>()
                    } else {
                        let mut val: Rc<Value> = valueOrError0.Extract();
                        Rc::new(Result::Success::<Rc<Structural<Rc<Value>>>, Rc<SerializationError>> {
                                value: crate::Std::JSON::Serializer::_default::MkStructural::<Rc<Value>>(&val)
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8793,3)
                pub fn DIGITS() -> CharSeq {
                    crate::Std::JSON::ByteStrConversion::_default::chars()
                }
                /// DafnyStandardLibraries-rs.dfy(8794,3)
                pub fn MINUS() -> u8 {
                    DafnyChar(char::from_u32(45).unwrap()).0 as u8
                }
                /// DafnyStandardLibraries-rs.dfy(8823,3)
                pub fn COLON() -> Rc<Structural<jcolon>> {
                    crate::Std::JSON::Serializer::_default::MkStructural::<View>(&crate::Std::JSON::Grammar::_default::COLON())
                }
                /// DafnyStandardLibraries-rs.dfy(8841,3)
                pub fn COMMA() -> Rc<Structural<jcomma>> {
                    crate::Std::JSON::Serializer::_default::MkStructural::<View>(&crate::Std::JSON::Grammar::_default::COMMA())
                }
            }

            /// DafnyStandardLibraries-rs.dfy(8903,3)
            pub type bytes32 = Sequence<u8>;

            /// DafnyStandardLibraries-rs.dfy(8906,3)
            pub type string32 = Sequence<DafnyChar>;
        }

        /// DafnyStandardLibraries-rs.dfy(8910,1)
        pub mod Spec {
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::DafnyChar;
            pub use ::dafny_runtime::int;
            pub use ::std::rc::Rc;
            pub use ::dafny_runtime::DafnyInt;
            pub use ::std::primitive::char;
            pub use ::dafny_runtime::integer_range;
            pub use ::dafny_runtime::Zero;
            pub use ::dafny_runtime::_System::nat;
            pub use ::dafny_runtime::seq;
            pub use ::dafny_runtime::truncate;
            pub use ::dafny_runtime::string_of;
            pub use crate::Std::Wrappers::Result;
            pub use crate::Std::JSON::Errors::SerializationError;
            pub use crate::Std::JSON::Values::Decimal;
            pub use crate::Std::JSON::Values::JSON;
            pub use crate::Std::JSON::Values::JSON::Null;
            pub use crate::Std::JSON::Values::JSON::Bool;
            pub use crate::Std::JSON::Values::JSON::String;
            pub use crate::Std::JSON::Values::JSON::Number;
            pub use crate::Std::JSON::Values::JSON::Object;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(8911,3)
                pub fn EscapeUnicode(c: u16) -> Sequence<u16> {
                    let mut sStr: Sequence<DafnyChar> = crate::Std::Strings::HexConversion::_default::OfNat(&int!((&c).clone()));
                    let mut s: Sequence<u16> = crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF16(&sStr);
                    ({
                        let _initializer = {
                                Rc::new(move |_v8: &DafnyInt| -> u16{
            DafnyChar(char::from_u32(48).unwrap()).0 as u16
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            };
                        integer_range(Zero::zero(), int!(4) - s.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                    }).concat(&s)
                }
                /// DafnyStandardLibraries-rs.dfy(8926,3)
                pub fn Escape(str: &Sequence<u16>, start: &nat) -> Sequence<u16> {
                    let mut _accumulator: Sequence<u16> = seq![] as Sequence<u16>;
                    let mut _r0 = str.clone();
                    let mut _r1 = start.clone();
                    'TAIL_CALL_START: loop {
                        let str = _r0;
                        let start = _r1;
                        if !(start.clone() < str.cardinality()) {
                            return _accumulator.concat(&(seq![] as Sequence<u16>));
                        } else {
                            _accumulator = _accumulator.concat(&(if str.get(&start) == truncate!(int!(34), u16) {
                                        crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF16(&string_of("\\\""))
                                    } else {
                                        if str.get(&start) == truncate!(int!(92), u16) {
                                            crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF16(&string_of("\\\\"))
                                        } else {
                                            if str.get(&start) == truncate!(int!(8), u16) {
                                                crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF16(&string_of("\\b"))
                                            } else {
                                                if str.get(&start) == truncate!(int!(12), u16) {
                                                    crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF16(&string_of("\\f"))
                                                } else {
                                                    if str.get(&start) == truncate!(int!(10), u16) {
                                                        crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF16(&string_of("\\n"))
                                                    } else {
                                                        if str.get(&start) == truncate!(int!(13), u16) {
                                                            crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF16(&string_of("\\r"))
                                                        } else {
                                                            if str.get(&start) == truncate!(int!(9), u16) {
                                                                crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF16(&string_of("\\t"))
                                                            } else {
                                                                {
                                                                    let __pat_let5_0: u16 = str.get(&start);
                                                                    {
                                                                        let c: u16 = __pat_let5_0;
                                                                        if c < truncate!(int!(31), u16) {
                                                                            crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF16(&string_of("\\u")).concat(&crate::Std::JSON::Spec::_default::EscapeUnicode(c))
                                                                        } else {
                                                                            seq![str.get(&start)]
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }));
                            let mut _in0: Sequence<u16> = str.clone();
                            let mut _in1: DafnyInt = start.clone() + int!(1);
                            _r0 = _in0.clone();
                            _r1 = _in1.clone();
                            continue 'TAIL_CALL_START;
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8935,3)
                pub fn EscapeToUTF8(str: &Sequence<DafnyChar>, start: &nat) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<u16>, Rc<SerializationError>>> = crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ToUTF16Checked(str).ToResult::<Rc<SerializationError>>(&Rc::new(SerializationError::InvalidUnicode {}));
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Sequence<u8>>()
                    } else {
                        let mut utf16: Sequence<u16> = valueOrError0.Extract();
                        let mut escaped: Sequence<u16> = crate::Std::JSON::Spec::_default::Escape(&utf16, &int!(0));
                        let mut valueOrError1: Rc<Result<Sequence<DafnyChar>, Rc<SerializationError>>> = crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::FromUTF16Checked(&escaped).ToOption().ToResult::<Rc<SerializationError>>(&Rc::new(SerializationError::InvalidUnicode {}));
                        if valueOrError1.IsFailure() {
                            valueOrError1.PropagateFailure::<Sequence<u8>>()
                        } else {
                            let mut utf32: Sequence<DafnyChar> = valueOrError1.Extract();
                            crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ToUTF8Checked(&utf32).ToResult::<Rc<SerializationError>>(&Rc::new(SerializationError::InvalidUnicode {}))
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8940,3)
                pub fn String(str: &Sequence<DafnyChar>) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<u8>, Rc<SerializationError>>> = crate::Std::JSON::Spec::_default::EscapeToUTF8(str, &int!(0));
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Sequence<u8>>()
                    } else {
                        let mut inBytes: Sequence<u8> = valueOrError0.Extract();
                        Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                value: crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("\"")).concat(&inBytes).concat(&crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("\"")))
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8961,3)
                pub fn IntToBytes(n: &DafnyInt) -> Sequence<u8> {
                    let mut s: Sequence<DafnyChar> = crate::Std::Strings::_default::OfInt(n);
                    crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&s)
                }
                /// DafnyStandardLibraries-rs.dfy(8968,3)
                pub fn Number(dec: &Rc<Decimal>) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                    Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                            value: crate::Std::JSON::Spec::_default::IntToBytes(dec.n()).concat(&(if dec.e10().clone() == int!(0) {
                                        seq![] as Sequence<u8>
                                    } else {
                                        crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("e")).concat(&crate::Std::JSON::Spec::_default::IntToBytes(dec.e10()))
                                    }))
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(8973,3)
                pub fn KeyValue(kv: &(Sequence<DafnyChar>, Rc<JSON>)) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<u8>, Rc<SerializationError>>> = crate::Std::JSON::Spec::_default::String(&kv.0.clone());
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Sequence<u8>>()
                    } else {
                        let mut key: Sequence<u8> = valueOrError0.Extract();
                        let mut valueOrError1: Rc<Result<Sequence<u8>, Rc<SerializationError>>> = crate::Std::JSON::Spec::_default::JSON(&kv.1.clone());
                        if valueOrError1.IsFailure() {
                            valueOrError1.PropagateFailure::<Sequence<u8>>()
                        } else {
                            let mut value: Sequence<u8> = valueOrError1.Extract();
                            Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                    value: key.concat(&crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of(":"))).concat(&value)
                                })
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8978,3)
                pub fn Join(sep: &Sequence<u8>, items: &Sequence<Rc<Result<Sequence<u8>, Rc<SerializationError>>>>) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                    if items.cardinality() == int!(0) {
                        Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                value: seq![] as Sequence<u8>
                            })
                    } else {
                        let mut valueOrError0: Rc<Result<Sequence<u8>, Rc<SerializationError>>> = items.get(&int!(0));
                        if valueOrError0.IsFailure() {
                            valueOrError0.PropagateFailure::<Sequence<u8>>()
                        } else {
                            let mut first: Sequence<u8> = valueOrError0.Extract();
                            if items.cardinality() == int!(1) {
                                Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                        value: first.clone()
                                    })
                            } else {
                                let mut valueOrError1: Rc<Result<Sequence<u8>, Rc<SerializationError>>> = crate::Std::JSON::Spec::_default::Join(sep, &items.drop(&int!(1)));
                                if valueOrError1.IsFailure() {
                                    valueOrError1.PropagateFailure::<Sequence<u8>>()
                                } else {
                                    let mut rest: Sequence<u8> = valueOrError1.Extract();
                                    Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                            value: first.concat(sep).concat(&rest)
                                        })
                                }
                            }
                        }
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8986,3)
                pub fn Object(obj: &Sequence<(Sequence<DafnyChar>, Rc<JSON>)>) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<u8>, Rc<SerializationError>>> = crate::Std::JSON::Spec::_default::Join(&crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of(",")), &({
                                let _initializer = {
                                        let obj: Sequence<(Sequence<DafnyChar>, Rc<JSON>)> = obj.clone();
                                        {
                                            let mut obj = obj.clone();
                                            Rc::new(move |i: &DafnyInt| -> Rc<Result<Sequence<u8>, Rc<SerializationError>>>{
            crate::Std::JSON::Spec::_default::KeyValue(&obj.get(i))
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }
                                    };
                                integer_range(Zero::zero(), obj.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                            }));
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Sequence<u8>>()
                    } else {
                        let mut middle: Sequence<u8> = valueOrError0.Extract();
                        Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                value: crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("{")).concat(&middle).concat(&crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("}")))
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8991,3)
                pub fn Array(arr: &Sequence<Rc<JSON>>) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                    let mut valueOrError0: Rc<Result<Sequence<u8>, Rc<SerializationError>>> = crate::Std::JSON::Spec::_default::Join(&crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of(",")), &({
                                let _initializer = {
                                        let arr: Sequence<Rc<JSON>> = arr.clone();
                                        {
                                            let mut arr = arr.clone();
                                            Rc::new(move |i: &DafnyInt| -> Rc<Result<Sequence<u8>, Rc<SerializationError>>>{
            crate::Std::JSON::Spec::_default::JSON(&arr.get(i))
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }
                                    };
                                integer_range(Zero::zero(), arr.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                            }));
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<Sequence<u8>>()
                    } else {
                        let mut middle: Sequence<u8> = valueOrError0.Extract();
                        Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                value: crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("[")).concat(&middle).concat(&crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("]")))
                            })
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(8996,3)
                pub fn JSON(js: &Rc<JSON>) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                    let mut _source0: Rc<JSON> = js.clone();
                    if matches!((&_source0).as_ref(), Null{ .. }) {
                        Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                value: crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("null"))
                            })
                    } else {
                        if matches!((&_source0).as_ref(), Bool{ .. }) {
                            let mut ___mcc_h0: bool = _source0.b().clone();
                            let mut b: bool = ___mcc_h0;
                            Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                    value: if b {
                                            crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("true"))
                                        } else {
                                            crate::Std::Unicode::UnicodeStringsWithUnicodeChar::_default::ASCIIToUTF8(&string_of("false"))
                                        }
                                })
                        } else {
                            if matches!((&_source0).as_ref(), String{ .. }) {
                                let mut ___mcc_h1: Sequence<DafnyChar> = _source0.str().clone();
                                let mut str: Sequence<DafnyChar> = ___mcc_h1.clone();
                                crate::Std::JSON::Spec::_default::String(&str)
                            } else {
                                if matches!((&_source0).as_ref(), Number{ .. }) {
                                    let mut ___mcc_h2: Rc<Decimal> = _source0.num().clone();
                                    let mut dec: Rc<Decimal> = ___mcc_h2.clone();
                                    crate::Std::JSON::Spec::_default::Number(&dec)
                                } else {
                                    if matches!((&_source0).as_ref(), Object{ .. }) {
                                        let mut ___mcc_h3: Sequence<(Sequence<DafnyChar>, Rc<JSON>)> = _source0.obj().clone();
                                        let mut obj: Sequence<(Sequence<DafnyChar>, Rc<JSON>)> = ___mcc_h3.clone();
                                        crate::Std::JSON::Spec::_default::Object(&obj)
                                    } else {
                                        let mut ___mcc_h4: Sequence<Rc<JSON>> = _source0.arr().clone();
                                        let mut arr: Sequence<Rc<JSON>> = ___mcc_h4.clone();
                                        crate::Std::JSON::Spec::_default::Array(&arr)
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        pub mod Utils {
            /// DafnyStandardLibraries-rs.dfy(9032,1)
            pub mod Cursors {
                pub use ::dafny_runtime::DafnyType;
                pub use ::std::fmt::Debug;
                pub use ::std::fmt::Formatter;
                pub use ::dafny_runtime::DafnyPrint;
                pub use ::std::rc::Rc;
                pub use ::dafny_runtime::upcast_id;
                pub use ::std::cmp::Eq;
                pub use ::std::hash::Hash;
                pub use ::std::cmp::PartialEq;
                pub use ::std::hash::Hasher;
                pub use ::std::convert::AsRef;
                pub use ::dafny_runtime::seq;
                pub use ::dafny_runtime::Sequence;
                pub use ::dafny_runtime::truncate;
                pub use ::dafny_runtime::int;
                pub use ::dafny_runtime::DafnyChar;
                pub use crate::Std::JSON::Utils::Cursors::CursorError::EOF;
                pub use ::dafny_runtime::string_of;
                pub use crate::Std::JSON::Utils::Cursors::CursorError::ExpectingByte;
                pub use crate::Std::JSON::Utils::Cursors::CursorError::ExpectingAnyByte;
                pub use ::dafny_runtime::DafnyInt;
                pub use ::dafny_runtime::integer_range;
                pub use ::dafny_runtime::Zero;
                pub use crate::Std::JSON::Utils::Views::Core::View;
                pub use crate::Std::JSON::Utils::Views::Core::View_;
                pub use crate::Std::JSON::Utils::Lexers::Core::LexerResult;
                pub use ::dafny_runtime::MaybePlacebo;
                pub use crate::Std::JSON::Utils::Lexers::Core::LexerResult::Accept;
                pub use crate::Std::JSON::Utils::Lexers::Core::LexerResult::Reject;

                /// DafnyStandardLibraries-rs.dfy(9041,3)
                #[derive(Clone)]
                pub enum Split<T: DafnyType> {
                    SP {
                        t: T,
                        cs: crate::Std::JSON::Utils::Cursors::FreshCursor
                    }
                }

                impl<T: DafnyType> Split<T> {
                    /// Returns a borrow of the field t
                    pub fn t(&self) -> &T {
                        match self {
                            Split::SP{t, cs, } => t,
                        }
                    }
                    /// Returns a borrow of the field cs
                    pub fn cs(&self) -> &crate::Std::JSON::Utils::Cursors::FreshCursor {
                        match self {
                            Split::SP{t, cs, } => cs,
                        }
                    }
                }

                impl<T: DafnyType> Debug
                    for Split<T> {
                    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                        DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl<T: DafnyType> DafnyPrint
                    for Split<T> {
                    fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                        match self {
                            Split::SP{t, cs, } => {
                                write!(_formatter, "Std.JSON.Utils.Cursors.Split.SP(")?;
                                DafnyPrint::fmt_print(t, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                DafnyPrint::fmt_print(cs, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            },
                        }
                    }
                }

                impl<T: DafnyType> Split<T> {
                    /// Given type parameter conversions, returns a lambda to convert this structure
                    pub fn coerce<__T0: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T) -> __T0 + 'static>) -> Rc<impl ::std::ops::Fn(Split<T>) -> Split<__T0>> {
                        Rc::new(move |this: Self| -> Split<__T0>{
                                match this {
                                    Split::SP{t, cs, } => {
                                        Split::SP {
                                            t: f_0.clone()(t),
                                            cs: upcast_id::<crate::Std::JSON::Utils::Cursors::FreshCursor>()(cs)
                                        }
                                    },
                                }
                            })
                    }
                }

                impl<T: DafnyType + Eq + Hash> PartialEq
                    for Split<T> {
                    fn eq(&self, other: &Self) -> bool {
                        match (
                                self,
                                other
                            ) {
                            (Split::SP{t, cs, }, Split::SP{t: _2_t, cs: _2_cs, }) => {
                                t == _2_t && cs == _2_cs
                            },
                            _ => {
                                false
                            },
                        }
                    }
                }

                impl<T: DafnyType + Eq + Hash> Eq
                    for Split<T> {}

                impl<T: DafnyType + Hash> Hash
                    for Split<T> {
                    fn hash<_H: Hasher>(&self, _state: &mut _H) {
                        match self {
                            Split::SP{t, cs, } => {
                                Hash::hash(t, _state);
                                Hash::hash(cs, _state)
                            },
                        }
                    }
                }

                impl<T: DafnyType> AsRef<Split<T>>
                    for Split<T> {
                    fn as_ref(&self) -> &Self {
                        self
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(9060,3)
                pub type Cursor = Rc<crate::Std::JSON::Utils::Cursors::Cursor_>;

                /// An element of Cursor
                pub fn __init_Cursor() -> Rc<crate::Std::JSON::Utils::Cursors::Cursor_> {
                    Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                            s: seq![] as Sequence<u8>,
                            beg: truncate!(int!(0), u32),
                            point: truncate!(int!(0), u32),
                            end: truncate!(int!(0), u32)
                        })
                }

                /// DafnyStandardLibraries-rs.dfy(9064,3)
                pub type FreshCursor = Rc<crate::Std::JSON::Utils::Cursors::Cursor_>;

                /// An element of FreshCursor
                pub fn __init_FreshCursor() -> Rc<crate::Std::JSON::Utils::Cursors::Cursor_> {
                    Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                            s: seq![] as Sequence<u8>,
                            beg: truncate!(int!(0), u32),
                            point: truncate!(int!(0), u32),
                            end: truncate!(int!(0), u32)
                        })
                }

                /// DafnyStandardLibraries-rs.dfy(9068,3)
                #[derive(Clone)]
                pub enum CursorError<R: DafnyType> {
                    EOF {},
                    ExpectingByte {
                        expected: u8,
                        b: i16
                    },
                    ExpectingAnyByte {
                        expected_sq: Sequence<u8>,
                        b: i16
                    },
                    OtherError {
                        err: R
                    }
                }

                impl<R: DafnyType> CursorError<R> {
                    /// DafnyStandardLibraries-rs.dfy(9069,5)
                    pub fn ToString(&self, pr: &Rc<dyn ::std::ops::Fn(&R) -> Sequence<DafnyChar>>) -> Sequence<DafnyChar> {
                        let mut _source0: Rc<crate::Std::JSON::Utils::Cursors::CursorError<R>> = Rc::new(self.clone());
                        if matches!((&_source0).as_ref(), EOF{ .. }) {
                            string_of("Reached EOF")
                        } else {
                            if matches!((&_source0).as_ref(), ExpectingByte{ .. }) {
                                let mut ___mcc_h0: u8 = _source0.expected().clone();
                                let mut ___mcc_h1: i16 = _source0.b().clone();
                                let mut b: i16 = ___mcc_h1;
                                let mut b0: u8 = ___mcc_h0;
                                let mut c: Sequence<DafnyChar> = if truncate!(int!(0), i16) < b {
                                        string_of("'").concat(&seq![DafnyChar(b as char)]).concat(&string_of("'"))
                                    } else {
                                        string_of("EOF")
                                    };
                                string_of("Expecting '").concat(&seq![DafnyChar(b0 as char)]).concat(&string_of("', read ")).concat(&c)
                            } else {
                                if matches!((&_source0).as_ref(), ExpectingAnyByte{ .. }) {
                                    let mut ___mcc_h2: Sequence<u8> = _source0.expected_sq().clone();
                                    let mut ___mcc_h3: i16 = _source0.b().clone();
                                    let mut b: i16 = ___mcc_h3;
                                    let mut bs0: Sequence<u8> = ___mcc_h2.clone();
                                    let mut c: Sequence<DafnyChar> = if truncate!(int!(0), i16) < b {
                                            string_of("'").concat(&seq![DafnyChar(b as char)]).concat(&string_of("'"))
                                        } else {
                                            string_of("EOF")
                                        };
                                    let mut c0s: Sequence<DafnyChar> = {
                                            let _initializer = {
                                                    let bs0: Sequence<u8> = bs0.clone();
                                                    {
                                                        let mut bs0 = bs0.clone();
                                                        Rc::new(move |idx: &DafnyInt| -> DafnyChar{
            DafnyChar(bs0.get(idx) as char)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                                    }
                                                };
                                            integer_range(Zero::zero(), bs0.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                                        };
                                    string_of("Expecting one of '").concat(&c0s).concat(&string_of("', read ")).concat(&c)
                                } else {
                                    let mut ___mcc_h4: R = _source0.err().clone();
                                    let mut err: R = ___mcc_h4.clone();
                                    pr(&err)
                                }
                            }
                        }
                    }
                    /// Gets the field expected for all enum members which have it
                    pub fn expected(&self) -> &u8 {
                        match self {
                            CursorError::EOF{} => panic!("field does not exist on this variant"),
                            CursorError::ExpectingByte{expected, b, } => expected,
                            CursorError::ExpectingAnyByte{expected_sq, b, } => panic!("field does not exist on this variant"),
                            CursorError::OtherError{err, } => panic!("field does not exist on this variant"),
                        }
                    }
                    /// Gets the field b for all enum members which have it
                    pub fn b(&self) -> &i16 {
                        match self {
                            CursorError::EOF{} => panic!("field does not exist on this variant"),
                            CursorError::ExpectingByte{expected, b, } => b,
                            CursorError::ExpectingAnyByte{expected_sq, b, } => b,
                            CursorError::OtherError{err, } => panic!("field does not exist on this variant"),
                        }
                    }
                    /// Gets the field expected_sq for all enum members which have it
                    pub fn expected_sq(&self) -> &Sequence<u8> {
                        match self {
                            CursorError::EOF{} => panic!("field does not exist on this variant"),
                            CursorError::ExpectingByte{expected, b, } => panic!("field does not exist on this variant"),
                            CursorError::ExpectingAnyByte{expected_sq, b, } => expected_sq,
                            CursorError::OtherError{err, } => panic!("field does not exist on this variant"),
                        }
                    }
                    /// Gets the field err for all enum members which have it
                    pub fn err(&self) -> &R {
                        match self {
                            CursorError::EOF{} => panic!("field does not exist on this variant"),
                            CursorError::ExpectingByte{expected, b, } => panic!("field does not exist on this variant"),
                            CursorError::ExpectingAnyByte{expected_sq, b, } => panic!("field does not exist on this variant"),
                            CursorError::OtherError{err, } => err,
                        }
                    }
                }

                impl<R: DafnyType> Debug
                    for CursorError<R> {
                    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                        DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl<R: DafnyType> DafnyPrint
                    for CursorError<R> {
                    fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                        match self {
                            CursorError::EOF{} => {
                                write!(_formatter, "Std.JSON.Utils.Cursors.CursorError.EOF")?;
                                Ok(())
                            },
                            CursorError::ExpectingByte{expected, b, } => {
                                write!(_formatter, "Std.JSON.Utils.Cursors.CursorError.ExpectingByte(")?;
                                DafnyPrint::fmt_print(expected, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                DafnyPrint::fmt_print(b, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            },
                            CursorError::ExpectingAnyByte{expected_sq, b, } => {
                                write!(_formatter, "Std.JSON.Utils.Cursors.CursorError.ExpectingAnyByte(")?;
                                DafnyPrint::fmt_print(expected_sq, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                DafnyPrint::fmt_print(b, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            },
                            CursorError::OtherError{err, } => {
                                write!(_formatter, "Std.JSON.Utils.Cursors.CursorError.OtherError(")?;
                                DafnyPrint::fmt_print(err, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            },
                        }
                    }
                }

                impl<R: DafnyType> CursorError<R> {
                    /// Given type parameter conversions, returns a lambda to convert this structure
                    pub fn coerce<__T0: DafnyType>(f_0: Rc<impl ::std::ops::Fn(R) -> __T0 + 'static>) -> Rc<impl ::std::ops::Fn(CursorError<R>) -> CursorError<__T0>> {
                        Rc::new(move |this: Self| -> CursorError<__T0>{
                                match this {
                                    CursorError::EOF{} => {
                                        CursorError::EOF {}
                                    },
                                    CursorError::ExpectingByte{expected, b, } => {
                                        CursorError::ExpectingByte {
                                            expected: upcast_id::<u8>()(expected),
                                            b: upcast_id::<i16>()(b)
                                        }
                                    },
                                    CursorError::ExpectingAnyByte{expected_sq, b, } => {
                                        CursorError::ExpectingAnyByte {
                                            expected_sq: upcast_id::<Sequence<u8>>()(expected_sq),
                                            b: upcast_id::<i16>()(b)
                                        }
                                    },
                                    CursorError::OtherError{err, } => {
                                        CursorError::OtherError {
                                            err: f_0.clone()(err)
                                        }
                                    },
                                }
                            })
                    }
                }

                impl<R: DafnyType + Eq + Hash> PartialEq
                    for CursorError<R> {
                    fn eq(&self, other: &Self) -> bool {
                        match (
                                self,
                                other
                            ) {
                            (CursorError::EOF{}, CursorError::EOF{}) => {
                                true
                            },
                            (CursorError::ExpectingByte{expected, b, }, CursorError::ExpectingByte{expected: _2_expected, b: _2_b, }) => {
                                expected == _2_expected && b == _2_b
                            },
                            (CursorError::ExpectingAnyByte{expected_sq, b, }, CursorError::ExpectingAnyByte{expected_sq: _2_expected_sq, b: _2_b, }) => {
                                expected_sq == _2_expected_sq && b == _2_b
                            },
                            (CursorError::OtherError{err, }, CursorError::OtherError{err: _2_err, }) => {
                                err == _2_err
                            },
                            _ => {
                                false
                            },
                        }
                    }
                }

                impl<R: DafnyType + Eq + Hash> Eq
                    for CursorError<R> {}

                impl<R: DafnyType + Hash> Hash
                    for CursorError<R> {
                    fn hash<_H: Hasher>(&self, _state: &mut _H) {
                        match self {
                            CursorError::EOF{} => {
                                
                            },
                            CursorError::ExpectingByte{expected, b, } => {
                                Hash::hash(expected, _state);
                                Hash::hash(b, _state)
                            },
                            CursorError::ExpectingAnyByte{expected_sq, b, } => {
                                Hash::hash(expected_sq, _state);
                                Hash::hash(b, _state)
                            },
                            CursorError::OtherError{err, } => {
                                Hash::hash(err, _state)
                            },
                        }
                    }
                }

                impl<R: DafnyType> AsRef<CursorError<R>>
                    for CursorError<R> {
                    fn as_ref(&self) -> &Self {
                        self
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(9088,3)
                #[derive(Clone)]
                pub enum Cursor_ {
                    Cursor {
                        s: Sequence<u8>,
                        beg: u32,
                        point: u32,
                        end: u32
                    }
                }

                impl Cursor_ {
                    /// DafnyStandardLibraries-rs.dfy(9093,5)
                    pub fn OfView(v: &View) -> crate::Std::JSON::Utils::Cursors::FreshCursor {
                        Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                                s: v.s().clone(),
                                beg: v.beg().clone(),
                                point: v.beg().clone(),
                                end: v.end().clone()
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(9098,5)
                    pub fn OfBytes(bs: &Sequence<u8>) -> crate::Std::JSON::Utils::Cursors::FreshCursor {
                        Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                                s: bs.clone(),
                                beg: truncate!(int!(0), u32),
                                point: truncate!(int!(0), u32),
                                end: truncate!(bs.cardinality(), u32)
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(9104,5)
                    pub fn Bytes(&self) -> Sequence<u8> {
                        self.s().slice(&int!(self.beg().clone()), &int!(self.end().clone()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(9155,5)
                    pub fn Prefix(&self) -> View {
                        Rc::new(View_::View {
                                s: self.s().clone(),
                                beg: self.beg().clone(),
                                end: self.point().clone()
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(9161,5)
                    pub fn Suffix(&self) -> crate::Std::JSON::Utils::Cursors::Cursor {
                        let mut _dt__update__tmp_h0: Rc<crate::Std::JSON::Utils::Cursors::Cursor_> = Rc::new(self.clone());
                        let mut _dt__update_hbeg_h0: u32 = self.point().clone();
                        Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                                s: _dt__update__tmp_h0.s().clone(),
                                beg: _dt__update_hbeg_h0,
                                point: _dt__update__tmp_h0.point().clone(),
                                end: _dt__update__tmp_h0.end().clone()
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(9167,5)
                    pub fn Split(&self) -> Rc<crate::Std::JSON::Utils::Cursors::Split<View>> {
                        Rc::new(crate::Std::JSON::Utils::Cursors::Split::SP::<View> {
                                t: self.Prefix(),
                                cs: self.Suffix()
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(9177,5)
                    pub fn PrefixLength(&self) -> u32 {
                        self.point().clone() - self.beg().clone()
                    }
                    /// DafnyStandardLibraries-rs.dfy(9183,5)
                    pub fn SuffixLength(&self) -> u32 {
                        self.end().clone() - self.point().clone()
                    }
                    /// DafnyStandardLibraries-rs.dfy(9189,5)
                    pub fn Length(&self) -> u32 {
                        self.end().clone() - self.beg().clone()
                    }
                    /// DafnyStandardLibraries-rs.dfy(9206,5)
                    pub fn At(&self, idx: u32) -> u8 {
                        self.s().get(&int!((&(self.beg().clone() + idx)).clone()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(9218,5)
                    pub fn SuffixAt(&self, idx: u32) -> u8 {
                        self.s().get(&int!((&(self.point().clone() + idx)).clone()))
                    }
                    /// DafnyStandardLibraries-rs.dfy(9225,5)
                    pub fn Peek(&self) -> i16 {
                        if self._EOF_q() {
                            truncate!(int!(-1), i16)
                        } else {
                            self.SuffixAt(truncate!(int!(0), u32)) as i16
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(9235,5)
                    pub fn LookingAt(&self, c: &DafnyChar) -> bool {
                        self.Peek() == c.clone().0 as i16
                    }
                    /// DafnyStandardLibraries-rs.dfy(9243,5)
                    pub fn Skip(&self, n: u32) -> crate::Std::JSON::Utils::Cursors::Cursor {
                        let mut _dt__update__tmp_h0: Rc<crate::Std::JSON::Utils::Cursors::Cursor_> = Rc::new(self.clone());
                        let mut _dt__update_hpoint_h0: u32 = self.point().clone() + n;
                        Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                                s: _dt__update__tmp_h0.s().clone(),
                                beg: _dt__update__tmp_h0.beg().clone(),
                                point: _dt__update_hpoint_h0,
                                end: _dt__update__tmp_h0.end().clone()
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(9252,5)
                    pub fn Unskip(&self, n: u32) -> crate::Std::JSON::Utils::Cursors::Cursor {
                        let mut _dt__update__tmp_h0: Rc<crate::Std::JSON::Utils::Cursors::Cursor_> = Rc::new(self.clone());
                        let mut _dt__update_hpoint_h0: u32 = self.point().clone() - n;
                        Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                                s: _dt__update__tmp_h0.s().clone(),
                                beg: _dt__update__tmp_h0.beg().clone(),
                                point: _dt__update_hpoint_h0,
                                end: _dt__update__tmp_h0.end().clone()
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(9259,5)
                    pub fn Get<_R: DafnyType>(&self, err: &_R) -> Rc<crate::Std::Wrappers::Result<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>>> {
                        if self._EOF_q() {
                            Rc::new(crate::Std::Wrappers::Result::Failure::<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>> {
                                    error: Rc::new(crate::Std::JSON::Utils::Cursors::CursorError::OtherError::<_R> {
                                                err: err.clone()
                                            })
                                })
                        } else {
                            Rc::new(crate::Std::Wrappers::Result::Success::<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>> {
                                    value: self.Skip(truncate!(int!(1), u32))
                                })
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(9269,5)
                    pub fn AssertByte<_R: DafnyType>(&self, b: u8) -> Rc<crate::Std::Wrappers::Result<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>>> {
                        let mut nxt: i16 = self.Peek();
                        if nxt == b as i16 {
                            Rc::new(crate::Std::Wrappers::Result::Success::<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>> {
                                    value: self.Skip(truncate!(int!(1), u32))
                                })
                        } else {
                            Rc::new(crate::Std::Wrappers::Result::Failure::<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>> {
                                    error: Rc::new(crate::Std::JSON::Utils::Cursors::CursorError::ExpectingByte::<_R> {
                                                expected: b,
                                                b: nxt
                                            })
                                })
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(9282,5)
                    pub fn AssertBytes<_R: DafnyType>(&self, bs: &Sequence<u8>, offset: u32) -> Rc<crate::Std::Wrappers::Result<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>>> {
                        let mut _this = Rc::new(self.clone());
                        let mut _r0 = bs.clone();
                        let mut _r1 = offset;
                        'TAIL_CALL_START: loop {
                            let bs = _r0;
                            let offset = _r1;
                            if offset == truncate!(bs.cardinality(), u32) {
                                return Rc::new(crate::Std::Wrappers::Result::Success::<Rc<crate::Std::JSON::Utils::Cursors::Cursor_>, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>> {
                                            value: _this.clone()
                                        });
                            } else {
                                let mut valueOrError0: Rc<crate::Std::Wrappers::Result<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>>> = _this.AssertByte::<_R>(bs.get(&int!((&offset).clone())));
                                if valueOrError0.IsFailure() {
                                    return valueOrError0.PropagateFailure::<Rc<crate::Std::JSON::Utils::Cursors::Cursor_>>();
                                } else {
                                    let mut ps: crate::Std::JSON::Utils::Cursors::Cursor = valueOrError0.Extract();
                                    let mut _in0: crate::Std::JSON::Utils::Cursors::Cursor = ps.clone();
                                    let mut _in1: Sequence<u8> = bs.clone();
                                    let mut _in2: u32 = offset + truncate!(int!(1), u32);
                                    _this = _in0.clone();
                                    _r0 = _in1.clone();
                                    _r1 = _in2;
                                    continue 'TAIL_CALL_START;
                                }
                            }
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(9298,5)
                    pub fn AssertChar<_R: DafnyType>(&self, c0: &DafnyChar) -> Rc<crate::Std::Wrappers::Result<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>>> {
                        self.AssertByte::<_R>(c0.clone().0 as u8)
                    }
                    /// DafnyStandardLibraries-rs.dfy(9306,5)
                    pub fn SkipByte(&self) -> crate::Std::JSON::Utils::Cursors::Cursor {
                        if self._EOF_q() {
                            Rc::new(self.clone())
                        } else {
                            self.Skip(truncate!(int!(1), u32))
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(9318,5)
                    pub fn SkipIf(&self, p: &Rc<dyn ::std::ops::Fn(&u8) -> bool>) -> crate::Std::JSON::Utils::Cursors::Cursor {
                        if self._EOF_q() || !p(&self.SuffixAt(truncate!(int!(0), u32))) {
                            Rc::new(self.clone())
                        } else {
                            self.Skip(truncate!(int!(1), u32))
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(9330,5)
                    pub fn SkipWhile(&self, p: &Rc<dyn ::std::ops::Fn(&u8) -> bool>) -> crate::Std::JSON::Utils::Cursors::Cursor {
                        let mut ps: crate::Std::JSON::Utils::Cursors::Cursor = Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                                    s: seq![] as Sequence<u8>,
                                    beg: truncate!(int!(0), u32),
                                    point: truncate!(int!(0), u32),
                                    end: truncate!(int!(0), u32)
                                });
                        let mut _point_k: u32 = self.point().clone();
                        let mut end: u32 = self.end().clone();
                        while _point_k < end && p(&self.s().get(&int!((&_point_k).clone()))) {
                            _point_k = _point_k + truncate!(int!(1), u32);
                        };
                        ps = Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                                    s: self.s().clone(),
                                    beg: self.beg().clone(),
                                    point: _point_k,
                                    end: self.end().clone()
                                });
                        return ps.clone();
                    }
                    /// DafnyStandardLibraries-rs.dfy(9352,5)
                    pub fn SkipWhileLexer<_A: DafnyType, _R: DafnyType>(&self, step: &Rc<dyn ::std::ops::Fn(&_A, &i16) -> Rc<LexerResult<_A, _R>>>, st: &_A) -> Rc<crate::Std::Wrappers::Result<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>>> {
                        let mut pr = MaybePlacebo::<Rc<crate::Std::Wrappers::Result<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>>>>::new();
                        let mut _point_k: u32 = self.point().clone();
                        let mut end: u32 = self.end().clone();
                        let mut _st_k: _A = st.clone();
                        while true {
                            let mut eof: bool = _point_k == end;
                            let mut minusone: i16 = truncate!(int!(-1), i16);
                            let mut c: i16;
                            if eof {
                                c = minusone;
                            } else {
                                c = self.s().get(&int!((&_point_k).clone())) as i16;
                            };
                            let mut _source0: Rc<LexerResult<_A, _R>> = step(&_st_k, &c);
                            if matches!((&_source0).as_ref(), Accept{ .. }) {
                                pr = MaybePlacebo::from(Rc::new(crate::Std::Wrappers::Result::Success::<Rc<crate::Std::JSON::Utils::Cursors::Cursor_>, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>> {
                                                value: Rc::new(crate::Std::JSON::Utils::Cursors::Cursor_::Cursor {
                                                            s: self.s().clone(),
                                                            beg: self.beg().clone(),
                                                            point: _point_k,
                                                            end: self.end().clone()
                                                        })
                                            }));
                                return pr.read();
                            } else {
                                if matches!((&_source0).as_ref(), Reject{ .. }) {
                                    let mut ___mcc_h0: _R = _source0.err().clone();
                                    let mut err: _R = ___mcc_h0.clone();
                                    pr = MaybePlacebo::from(Rc::new(crate::Std::Wrappers::Result::Failure::<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>> {
                                                    error: Rc::new(crate::Std::JSON::Utils::Cursors::CursorError::OtherError::<_R> {
                                                                err: err.clone()
                                                            })
                                                }));
                                    return pr.read();
                                } else {
                                    let mut ___mcc_h1: _A = _source0.st().clone();
                                    let mut _st_k_k: _A = ___mcc_h1.clone();
                                    if eof {
                                        pr = MaybePlacebo::from(Rc::new(crate::Std::Wrappers::Result::Failure::<crate::Std::JSON::Utils::Cursors::Cursor, Rc<crate::Std::JSON::Utils::Cursors::CursorError<_R>>> {
                                                        error: Rc::new(crate::Std::JSON::Utils::Cursors::CursorError::EOF::<_R> {})
                                                    }));
                                        return pr.read();
                                    } else {
                                        _st_k = _st_k_k.clone();
                                        _point_k = _point_k + truncate!(int!(1), u32);
                                    }
                                }
                            }
                        };
                        return pr.read();
                    }
                    /// DafnyStandardLibraries-rs.dfy(9090,5)
                    pub fn _BOF_q(&self) -> bool {
                        self.point().clone() == self.beg().clone()
                    }
                    /// DafnyStandardLibraries-rs.dfy(9091,5)
                    pub fn _EOF_q(&self) -> bool {
                        self.point().clone() == self.end().clone()
                    }
                    /// Returns a borrow of the field s
                    pub fn s(&self) -> &Sequence<u8> {
                        match self {
                            Cursor_::Cursor{s, beg, point, end, } => s,
                        }
                    }
                    /// Returns a borrow of the field beg
                    pub fn beg(&self) -> &u32 {
                        match self {
                            Cursor_::Cursor{s, beg, point, end, } => beg,
                        }
                    }
                    /// Returns a borrow of the field point
                    pub fn point(&self) -> &u32 {
                        match self {
                            Cursor_::Cursor{s, beg, point, end, } => point,
                        }
                    }
                    /// Returns a borrow of the field end
                    pub fn end(&self) -> &u32 {
                        match self {
                            Cursor_::Cursor{s, beg, point, end, } => end,
                        }
                    }
                }

                impl Debug
                    for Cursor_ {
                    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                        DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint
                    for Cursor_ {
                    fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                        match self {
                            Cursor_::Cursor{s, beg, point, end, } => {
                                write!(_formatter, "Std.JSON.Utils.Cursors.Cursor__.Cursor(")?;
                                DafnyPrint::fmt_print(s, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                DafnyPrint::fmt_print(beg, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                DafnyPrint::fmt_print(point, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                DafnyPrint::fmt_print(end, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            },
                        }
                    }
                }

                impl PartialEq
                    for Cursor_ {
                    fn eq(&self, other: &Self) -> bool {
                        match (
                                self,
                                other
                            ) {
                            (Cursor_::Cursor{s, beg, point, end, }, Cursor_::Cursor{s: _2_s, beg: _2_beg, point: _2_point, end: _2_end, }) => {
                                s == _2_s && beg == _2_beg && point == _2_point && end == _2_end
                            },
                            _ => {
                                false
                            },
                        }
                    }
                }

                impl Eq
                    for Cursor_ {}

                impl Hash
                    for Cursor_ {
                    fn hash<_H: Hasher>(&self, _state: &mut _H) {
                        match self {
                            Cursor_::Cursor{s, beg, point, end, } => {
                                Hash::hash(s, _state);
                                Hash::hash(beg, _state);
                                Hash::hash(point, _state);
                                Hash::hash(end, _state)
                            },
                        }
                    }
                }

                impl AsRef<Cursor_>
                    for Cursor_ {
                    fn as_ref(&self) -> &Self {
                        self
                    }
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9396,1)
            pub mod Lexers {
                /// DafnyStandardLibraries-rs.dfy(9398,3)
                pub mod Core {
                    pub use ::dafny_runtime::DafnyType;
                    pub use ::std::fmt::Debug;
                    pub use ::std::fmt::Formatter;
                    pub use ::std::fmt::Result;
                    pub use ::dafny_runtime::DafnyPrint;
                    pub use ::std::rc::Rc;
                    pub use ::std::cmp::Eq;
                    pub use ::std::hash::Hash;
                    pub use ::std::cmp::PartialEq;
                    pub use ::std::hash::Hasher;
                    pub use ::std::convert::AsRef;

                    /// DafnyStandardLibraries-rs.dfy(9403,5)
                    #[derive(Clone)]
                    pub enum LexerResult<T: DafnyType, R: DafnyType> {
                        Accept {},
                        Reject {
                            err: R
                        },
                        Partial {
                            st: T
                        }
                    }

                    impl<T: DafnyType, R: DafnyType> LexerResult<T, R> {
                        /// Gets the field err for all enum members which have it
                        pub fn err(&self) -> &R {
                            match self {
                                LexerResult::Accept{} => panic!("field does not exist on this variant"),
                                LexerResult::Reject{err, } => err,
                                LexerResult::Partial{st, } => panic!("field does not exist on this variant"),
                            }
                        }
                        /// Gets the field st for all enum members which have it
                        pub fn st(&self) -> &T {
                            match self {
                                LexerResult::Accept{} => panic!("field does not exist on this variant"),
                                LexerResult::Reject{err, } => panic!("field does not exist on this variant"),
                                LexerResult::Partial{st, } => st,
                            }
                        }
                    }

                    impl<T: DafnyType, R: DafnyType> Debug
                        for LexerResult<T, R> {
                        fn fmt(&self, f: &mut Formatter) -> Result {
                            DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl<T: DafnyType, R: DafnyType> DafnyPrint
                        for LexerResult<T, R> {
                        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                            match self {
                                LexerResult::Accept{} => {
                                    write!(_formatter, "Std.JSON.Utils.Lexers.Core.LexerResult.Accept")?;
                                    Ok(())
                                },
                                LexerResult::Reject{err, } => {
                                    write!(_formatter, "Std.JSON.Utils.Lexers.Core.LexerResult.Reject(")?;
                                    DafnyPrint::fmt_print(err, _formatter, false)?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                },
                                LexerResult::Partial{st, } => {
                                    write!(_formatter, "Std.JSON.Utils.Lexers.Core.LexerResult.Partial(")?;
                                    DafnyPrint::fmt_print(st, _formatter, false)?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                },
                            }
                        }
                    }

                    impl<T: DafnyType, R: DafnyType> LexerResult<T, R> {
                        /// Given type parameter conversions, returns a lambda to convert this structure
                        pub fn coerce<__T0: DafnyType, __T1: DafnyType>(f_0: Rc<impl ::std::ops::Fn(T) -> __T0 + 'static>, f_1: Rc<impl ::std::ops::Fn(R) -> __T1 + 'static>) -> Rc<impl ::std::ops::Fn(LexerResult<T, R>) -> LexerResult<__T0, __T1>> {
                            Rc::new(move |this: Self| -> LexerResult<__T0, __T1>{
                                    match this {
                                        LexerResult::Accept{} => {
                                            LexerResult::Accept {}
                                        },
                                        LexerResult::Reject{err, } => {
                                            LexerResult::Reject {
                                                err: f_1.clone()(err)
                                            }
                                        },
                                        LexerResult::Partial{st, } => {
                                            LexerResult::Partial {
                                                st: f_0.clone()(st)
                                            }
                                        },
                                    }
                                })
                        }
                    }

                    impl<T: DafnyType + Eq + Hash, R: DafnyType + Eq + Hash> PartialEq
                        for LexerResult<T, R> {
                        fn eq(&self, other: &Self) -> bool {
                            match (
                                    self,
                                    other
                                ) {
                                (LexerResult::Accept{}, LexerResult::Accept{}) => {
                                    true
                                },
                                (LexerResult::Reject{err, }, LexerResult::Reject{err: _2_err, }) => {
                                    err == _2_err
                                },
                                (LexerResult::Partial{st, }, LexerResult::Partial{st: _2_st, }) => {
                                    st == _2_st
                                },
                                _ => {
                                    false
                                },
                            }
                        }
                    }

                    impl<T: DafnyType + Eq + Hash, R: DafnyType + Eq + Hash> Eq
                        for LexerResult<T, R> {}

                    impl<T: DafnyType + Hash, R: DafnyType + Hash> Hash
                        for LexerResult<T, R> {
                        fn hash<_H: Hasher>(&self, _state: &mut _H) {
                            match self {
                                LexerResult::Accept{} => {
                                    
                                },
                                LexerResult::Reject{err, } => {
                                    Hash::hash(err, _state)
                                },
                                LexerResult::Partial{st, } => {
                                    Hash::hash(st, _state)
                                },
                            }
                        }
                    }

                    impl<T: DafnyType, R: DafnyType> AsRef<LexerResult<T, R>>
                        for LexerResult<T, R> {
                        fn as_ref(&self) -> &Self {
                            self
                        }
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(9408,3)
                pub mod Strings {
                    pub use ::dafny_runtime::DafnyType;
                    pub use ::std::rc::Rc;
                    pub use crate::Std::JSON::Utils::Lexers::Core::LexerResult;
                    pub use ::dafny_runtime::DafnyChar;
                    pub use ::std::primitive::char;
                    pub use ::dafny_runtime::Sequence;
                    pub use crate::Std::JSON::Utils::Lexers::Strings::StringLexerState::Start;
                    pub use ::dafny_runtime::string_of;
                    pub use crate::Std::JSON::Utils::Lexers::Strings::StringLexerState::Body;
                    pub use ::std::fmt::Debug;
                    pub use ::std::fmt::Formatter;
                    pub use ::std::fmt::Result;
                    pub use ::dafny_runtime::DafnyPrint;
                    pub use ::std::cmp::PartialEq;
                    pub use ::std::cmp::Eq;
                    pub use ::std::hash::Hash;
                    pub use ::std::hash::Hasher;
                    pub use ::std::convert::AsRef;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(9411,5)
                        pub fn StringBody<_R: DafnyType>(escaped: bool, byte: i16) -> Rc<LexerResult<bool, _R>> {
                            if byte == DafnyChar(char::from_u32(92).unwrap()).0 as i16 {
                                Rc::new(LexerResult::Partial::<bool, _R> {
                                        st: !escaped
                                    })
                            } else {
                                if byte == DafnyChar(char::from_u32(34).unwrap()).0 as i16 && !escaped {
                                    Rc::new(LexerResult::Accept::<bool, _R> {})
                                } else {
                                    Rc::new(LexerResult::Partial::<bool, _R> {
                                            st: false
                                        })
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9423,5)
                        pub fn String(st: &Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState>, byte: i16) -> Rc<LexerResult<Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState>, Sequence<DafnyChar>>> {
                            let mut _source0: Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState> = st.clone();
                            if matches!((&_source0).as_ref(), Start{ .. }) {
                                if byte == DafnyChar(char::from_u32(34).unwrap()).0 as i16 {
                                    Rc::new(LexerResult::Partial::<Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState>, Sequence<DafnyChar>> {
                                            st: Rc::new(crate::Std::JSON::Utils::Lexers::Strings::StringLexerState::Body {
                                                        escaped: false
                                                    })
                                        })
                                } else {
                                    Rc::new(LexerResult::Reject::<Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState>, Sequence<DafnyChar>> {
                                            err: string_of("String must start with double quote")
                                        })
                                }
                            } else {
                                if matches!((&_source0).as_ref(), Body{ .. }) {
                                    let mut ___mcc_h0: bool = _source0.escaped().clone();
                                    let mut escaped: bool = ___mcc_h0;
                                    if byte == DafnyChar(char::from_u32(92).unwrap()).0 as i16 {
                                        Rc::new(LexerResult::Partial::<Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState>, Sequence<DafnyChar>> {
                                                st: Rc::new(crate::Std::JSON::Utils::Lexers::Strings::StringLexerState::Body {
                                                            escaped: !escaped
                                                        })
                                            })
                                    } else {
                                        if byte == DafnyChar(char::from_u32(34).unwrap()).0 as i16 && !escaped {
                                            Rc::new(LexerResult::Partial::<Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState>, Sequence<DafnyChar>> {
                                                    st: Rc::new(crate::Std::JSON::Utils::Lexers::Strings::StringLexerState::End {})
                                                })
                                        } else {
                                            Rc::new(LexerResult::Partial::<Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState>, Sequence<DafnyChar>> {
                                                    st: Rc::new(crate::Std::JSON::Utils::Lexers::Strings::StringLexerState::Body {
                                                                escaped: false
                                                            })
                                                })
                                        }
                                    }
                                } else {
                                    Rc::new(LexerResult::Accept::<Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState>, Sequence<DafnyChar>> {})
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9409,5)
                        pub fn StringBodyLexerStart() -> bool {
                            false
                        }
                        /// DafnyStandardLibraries-rs.dfy(9421,5)
                        pub fn StringLexerStart() -> Rc<crate::Std::JSON::Utils::Lexers::Strings::StringLexerState> {
                            Rc::new(crate::Std::JSON::Utils::Lexers::Strings::StringLexerState::Start {})
                        }
                    }

                    /// DafnyStandardLibraries-rs.dfy(9448,5)
                    #[derive(Clone)]
                    pub enum StringLexerState {
                        Start {},
                        Body {
                            escaped: bool
                        },
                        End {}
                    }

                    impl StringLexerState {
                        /// Gets the field escaped for all enum members which have it
                        pub fn escaped(&self) -> &bool {
                            match self {
                                StringLexerState::Start{} => panic!("field does not exist on this variant"),
                                StringLexerState::Body{escaped, } => escaped,
                                StringLexerState::End{} => panic!("field does not exist on this variant"),
                            }
                        }
                    }

                    impl Debug
                        for StringLexerState {
                        fn fmt(&self, f: &mut Formatter) -> Result {
                            DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint
                        for StringLexerState {
                        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                            match self {
                                StringLexerState::Start{} => {
                                    write!(_formatter, "Std.JSON.Utils.Lexers.Strings.StringLexerState.Start")?;
                                    Ok(())
                                },
                                StringLexerState::Body{escaped, } => {
                                    write!(_formatter, "Std.JSON.Utils.Lexers.Strings.StringLexerState.Body(")?;
                                    DafnyPrint::fmt_print(escaped, _formatter, false)?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                },
                                StringLexerState::End{} => {
                                    write!(_formatter, "Std.JSON.Utils.Lexers.Strings.StringLexerState.End")?;
                                    Ok(())
                                },
                            }
                        }
                    }

                    impl PartialEq
                        for StringLexerState {
                        fn eq(&self, other: &Self) -> bool {
                            match (
                                    self,
                                    other
                                ) {
                                (StringLexerState::Start{}, StringLexerState::Start{}) => {
                                    true
                                },
                                (StringLexerState::Body{escaped, }, StringLexerState::Body{escaped: _2_escaped, }) => {
                                    escaped == _2_escaped
                                },
                                (StringLexerState::End{}, StringLexerState::End{}) => {
                                    true
                                },
                                _ => {
                                    false
                                },
                            }
                        }
                    }

                    impl Eq
                        for StringLexerState {}

                    impl Hash
                        for StringLexerState {
                        fn hash<_H: Hasher>(&self, _state: &mut _H) {
                            match self {
                                StringLexerState::Start{} => {
                                    
                                },
                                StringLexerState::Body{escaped, } => {
                                    Hash::hash(escaped, _state)
                                },
                                StringLexerState::End{} => {
                                    
                                },
                            }
                        }
                    }

                    impl AsRef<StringLexerState>
                        for StringLexerState {
                        fn as_ref(&self) -> &Self {
                            self
                        }
                    }
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9452,1)
            pub mod Parsers {
                pub use ::dafny_runtime::DafnyType;
                pub use ::std::rc::Rc;
                pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                pub use crate::Std::JSON::Utils::Cursors::Split;
                pub use crate::Std::JSON::Utils::Cursors::CursorError;
                pub use ::std::default::Default;
                pub use ::std::fmt::Debug;
                pub use ::std::fmt::Formatter;
                pub use ::dafny_runtime::DafnyPrint;
                pub use ::dafny_runtime::fn1_coerce;
                pub use ::dafny_runtime::rc_coerce;
                pub use ::dafny_runtime::upcast_id;
                pub use ::std::convert::AsRef;

                pub struct _default {}

                impl _default {
                    /// DafnyStandardLibraries-rs.dfy(9453,3)
                    pub fn ParserWitness<_T: DafnyType, _R: DafnyType>() -> Rc<crate::Std::JSON::Utils::Parsers::Parser_<_T, _R>> {
                        Rc::new(crate::Std::JSON::Utils::Parsers::Parser_::Parser::<_T, _R> {
                                r#fn: {
                                        Rc::new(move |_v9: &FreshCursor| -> Rc<crate::Std::Wrappers::Result<Rc<Split<_T>>, Rc<CursorError<_R>>>>{
            Rc::new(crate::Std::Wrappers::Result::Failure::<Rc<Split<_T>>, Rc<CursorError<_R>>> {
                    error: Rc::new(CursorError::EOF::<_R> {})
                })
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                    }
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(9459,3)
                    pub fn SubParserWitness<_T: DafnyType, _R: DafnyType>() -> Rc<crate::Std::JSON::Utils::Parsers::SubParser_<_T, _R>> {
                        Rc::new(crate::Std::JSON::Utils::Parsers::SubParser_::SubParser::<_T, _R> {
                                r#fn: {
                                        Rc::new(move |cs: &FreshCursor| -> Rc<crate::Std::Wrappers::Result<Rc<Split<_T>>, Rc<CursorError<_R>>>>{
            Rc::new(crate::Std::Wrappers::Result::Failure::<Rc<Split<_T>>, Rc<CursorError<_R>>> {
                    error: Rc::new(CursorError::EOF::<_R> {})
                })
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                    }
                            })
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(9475,3)
                pub type Parser<T: DafnyType, R: DafnyType> = Rc<crate::Std::JSON::Utils::Parsers::Parser_<T, R>>;

                /// An element of Parser
                pub fn __init_Parser<T: DafnyType + Default, R: DafnyType + Default>() -> Rc<crate::Std::JSON::Utils::Parsers::Parser_<T, R>> {
                    crate::Std::JSON::Utils::Parsers::_default::ParserWitness::<T, R>()
                }

                /// DafnyStandardLibraries-rs.dfy(9479,3)
                #[derive(Clone)]
                pub enum Parser_<T: DafnyType, R: DafnyType> {
                    Parser {
                        r#fn: Rc<dyn ::std::ops::Fn(&FreshCursor) -> Rc<crate::Std::Wrappers::Result<Rc<Split<T>>, Rc<CursorError<R>>>>>
                    }
                }

                impl<T: DafnyType, R: DafnyType> Parser_<T, R> {
                    /// Returns a borrow of the field r#fn
                    pub fn r#fn(&self) -> &Rc<dyn ::std::ops::Fn(&FreshCursor) -> Rc<crate::Std::Wrappers::Result<Rc<Split<T>>, Rc<CursorError<R>>>>> {
                        match self {
                            Parser_::Parser{r#fn, } => r#fn,
                        }
                    }
                }

                impl<T: DafnyType, R: DafnyType> Debug
                    for Parser_<T, R> {
                    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                        DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl<T: DafnyType, R: DafnyType> DafnyPrint
                    for Parser_<T, R> {
                    fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                        match self {
                            Parser_::Parser{r#fn, } => {
                                write!(_formatter, "Std.JSON.Utils.Parsers.Parser__.Parser(")?;
                                write!(_formatter, "<function>")?;
                                write!(_formatter, ")")?;
                                Ok(())
                            },
                        }
                    }
                }

                impl<T: DafnyType, R: DafnyType> Parser_<T, R> {
                    /// Given type parameter conversions, returns a lambda to convert this structure
                    pub fn coerce<__T1: DafnyType>(f_1: Rc<impl ::std::ops::Fn(R) -> __T1 + 'static>) -> Rc<impl ::std::ops::Fn(Parser_<T, R>) -> Parser_<T, __T1>> {
                        Rc::new(move |this: Self| -> Parser_<T, __T1>{
                                match this {
                                    Parser_::Parser{r#fn, } => {
                                        Parser_::Parser {
                                            r#fn: fn1_coerce::<FreshCursor, Rc<crate::Std::Wrappers::Result<Rc<Split<T>>, Rc<CursorError<R>>>>, Rc<crate::Std::Wrappers::Result<Rc<Split<T>>, Rc<CursorError<__T1>>>>>(rc_coerce(crate::Std::Wrappers::Result::<Rc<Split<T>>, Rc<CursorError<R>>>::coerce(upcast_id::<Rc<Split<T>>>(), rc_coerce(CursorError::<R>::coerce(f_1.clone())))))(r#fn)
                                        }
                                    },
                                }
                            })
                    }
                }

                impl<T: DafnyType, R: DafnyType> AsRef<Parser_<T, R>>
                    for Parser_<T, R> {
                    fn as_ref(&self) -> &Self {
                        self
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(9488,3)
                #[derive(Clone)]
                pub enum SubParser_<T: DafnyType, R: DafnyType> {
                    SubParser {
                        r#fn: Rc<dyn ::std::ops::Fn(&FreshCursor) -> Rc<crate::Std::Wrappers::Result<Rc<Split<T>>, Rc<CursorError<R>>>>>
                    }
                }

                impl<T: DafnyType, R: DafnyType> SubParser_<T, R> {
                    /// Returns a borrow of the field r#fn
                    pub fn r#fn(&self) -> &Rc<dyn ::std::ops::Fn(&FreshCursor) -> Rc<crate::Std::Wrappers::Result<Rc<Split<T>>, Rc<CursorError<R>>>>> {
                        match self {
                            SubParser_::SubParser{r#fn, } => r#fn,
                        }
                    }
                }

                impl<T: DafnyType, R: DafnyType> Debug
                    for SubParser_<T, R> {
                    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
                        DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl<T: DafnyType, R: DafnyType> DafnyPrint
                    for SubParser_<T, R> {
                    fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                        match self {
                            SubParser_::SubParser{r#fn, } => {
                                write!(_formatter, "Std.JSON.Utils.Parsers.SubParser__.SubParser(")?;
                                write!(_formatter, "<function>")?;
                                write!(_formatter, ")")?;
                                Ok(())
                            },
                        }
                    }
                }

                impl<T: DafnyType, R: DafnyType> SubParser_<T, R> {
                    /// Given type parameter conversions, returns a lambda to convert this structure
                    pub fn coerce<__T1: DafnyType>(f_1: Rc<impl ::std::ops::Fn(R) -> __T1 + 'static>) -> Rc<impl ::std::ops::Fn(SubParser_<T, R>) -> SubParser_<T, __T1>> {
                        Rc::new(move |this: Self| -> SubParser_<T, __T1>{
                                match this {
                                    SubParser_::SubParser{r#fn, } => {
                                        SubParser_::SubParser {
                                            r#fn: fn1_coerce::<FreshCursor, Rc<crate::Std::Wrappers::Result<Rc<Split<T>>, Rc<CursorError<R>>>>, Rc<crate::Std::Wrappers::Result<Rc<Split<T>>, Rc<CursorError<__T1>>>>>(rc_coerce(crate::Std::Wrappers::Result::<Rc<Split<T>>, Rc<CursorError<R>>>::coerce(upcast_id::<Rc<Split<T>>>(), rc_coerce(CursorError::<R>::coerce(f_1.clone())))))(r#fn)
                                        }
                                    },
                                }
                            })
                    }
                }

                impl<T: DafnyType, R: DafnyType> AsRef<SubParser_<T, R>>
                    for SubParser_<T, R> {
                    fn as_ref(&self) -> &Self {
                        self
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(9501,3)
                pub type SubParser<T: DafnyType, R: DafnyType> = Rc<crate::Std::JSON::Utils::Parsers::SubParser_<T, R>>;

                /// An element of SubParser
                pub fn __init_SubParser<T: DafnyType + Default, R: DafnyType + Default>() -> Rc<crate::Std::JSON::Utils::Parsers::SubParser_<T, R>> {
                    crate::Std::JSON::Utils::Parsers::_default::SubParserWitness::<T, R>()
                }
            }

            pub mod Views {
                /// DafnyStandardLibraries-rs.dfy(9506,1)
                pub mod Core {
                    pub use ::std::rc::Rc;
                    pub use ::dafny_runtime::seq;
                    pub use ::dafny_runtime::Sequence;
                    pub use ::dafny_runtime::truncate;
                    pub use ::dafny_runtime::int;
                    pub use ::dafny_runtime::DafnyChar;
                    pub use ::dafny_runtime::DafnyInt;
                    pub use ::dafny_runtime::integer_range;
                    pub use ::dafny_runtime::Zero;
                    pub use ::std::default::Default;
                    pub use ::dafny_runtime::Object;
                    pub use ::std::convert::Into;
                    pub use ::dafny_runtime::DafnyUsize;
                    pub use ::std::fmt::Debug;
                    pub use ::std::fmt::Formatter;
                    pub use ::std::fmt::Result;
                    pub use ::dafny_runtime::DafnyPrint;
                    pub use ::std::cmp::PartialEq;
                    pub use ::std::cmp::Eq;
                    pub use ::std::hash::Hash;
                    pub use ::std::hash::Hasher;
                    pub use ::std::convert::AsRef;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(9507,3)
                        pub fn Adjacent(lv: &crate::Std::JSON::Utils::Views::Core::View, rv: &crate::Std::JSON::Utils::Views::Core::View) -> bool {
                            lv.end().clone() == rv.beg().clone() && lv.s().clone() == rv.s().clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(9513,3)
                        pub fn Merge(lv: &crate::Std::JSON::Utils::Views::Core::View, rv: &crate::Std::JSON::Utils::Views::Core::View) -> crate::Std::JSON::Utils::Views::Core::View {
                            let mut _dt__update__tmp_h0: crate::Std::JSON::Utils::Views::Core::View = lv.clone();
                            let mut _dt__update_hend_h0: u32 = rv.end().clone();
                            Rc::new(crate::Std::JSON::Utils::Views::Core::View_::View {
                                    s: _dt__update__tmp_h0.s().clone(),
                                    beg: _dt__update__tmp_h0.beg().clone(),
                                    end: _dt__update_hend_h0
                                })
                        }
                    }

                    /// DafnyStandardLibraries-rs.dfy(9522,3)
                    pub type View = Rc<crate::Std::JSON::Utils::Views::Core::View_>;

                    /// An element of View
                    pub fn __init_View() -> Rc<crate::Std::JSON::Utils::Views::Core::View_> {
                        Rc::new(crate::Std::JSON::Utils::Views::Core::View_::View {
                                s: seq![] as Sequence<u8>,
                                beg: truncate!(int!(0), u32),
                                end: truncate!(int!(0), u32)
                            })
                    }

                    /// DafnyStandardLibraries-rs.dfy(9526,3)
                    #[derive(Clone)]
                    pub enum View_ {
                        View {
                            s: Sequence<u8>,
                            beg: u32,
                            end: u32
                        }
                    }

                    impl View_ {
                        /// DafnyStandardLibraries-rs.dfy(9531,5)
                        pub fn Length(&self) -> u32 {
                            self.end().clone() - self.beg().clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(9537,5)
                        pub fn Bytes(&self) -> Sequence<u8> {
                            self.s().slice(&int!(self.beg().clone()), &int!(self.end().clone()))
                        }
                        /// DafnyStandardLibraries-rs.dfy(9543,5)
                        pub fn OfBytes(bs: &Sequence<u8>) -> crate::Std::JSON::Utils::Views::Core::View {
                            Rc::new(crate::Std::JSON::Utils::Views::Core::View_::View {
                                    s: bs.clone(),
                                    beg: truncate!(int!(0), u32),
                                    end: truncate!(bs.cardinality(), u32)
                                })
                        }
                        /// DafnyStandardLibraries-rs.dfy(9550,5)
                        pub fn OfString(s: &Sequence<DafnyChar>) -> Sequence<u8> {
                            {
                                let _initializer = {
                                        let s: Sequence<DafnyChar> = s.clone();
                                        {
                                            let mut s = s.clone();
                                            Rc::new(move |i: &DafnyInt| -> u8{
            s.get(i).0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }
                                    };
                                integer_range(Zero::zero(), s.cardinality()).map(move |i| _initializer(&i)).collect::<Sequence<_>>()
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9577,5)
                        pub fn _Byte_q(&self, c: u8) -> bool {
                            let mut _hresult: bool = <bool as Default>::default();
                            _hresult = self.Length() == truncate!(int!(1), u32) && self.At(truncate!(int!(0), u32)) == c;
                            return _hresult;
                        }
                        /// DafnyStandardLibraries-rs.dfy(9585,5)
                        pub fn _Char_q(&self, c: &DafnyChar) -> bool {
                            self._Byte_q(c.clone().0 as u8)
                        }
                        /// DafnyStandardLibraries-rs.dfy(9597,5)
                        pub fn At(&self, idx: u32) -> u8 {
                            self.s().get(&int!((&(self.beg().clone() + idx)).clone()))
                        }
                        /// DafnyStandardLibraries-rs.dfy(9604,5)
                        pub fn Peek(&self) -> i16 {
                            if self._Empty_q() {
                                truncate!(int!(-1), i16)
                            } else {
                                self.At(truncate!(int!(0), u32)) as i16
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9614,5)
                        pub fn CopyTo(&self, dest: &Object<[u8]>, start: u32) -> () {
                            let mut _hi0: u32 = self.Length();
                            for idx in integer_range(truncate!(int!(0), u32), _hi0).map(Into::<u32>::into) {
                                {
                                    let __idx0 = DafnyUsize::into_usize(start + idx);
                                    ::dafny_runtime::md!(dest)[__idx0] = self.s().get(&int!((&(self.beg().clone() + idx)).clone()));
                                }
                            }
                            return ();
                        }
                        /// DafnyStandardLibraries-rs.dfy(9528,5)
                        pub fn Empty() -> crate::Std::JSON::Utils::Views::Core::View {
                            Rc::new(crate::Std::JSON::Utils::Views::Core::View_::View {
                                    s: seq![] as Sequence<u8>,
                                    beg: truncate!(int!(0), u32),
                                    end: truncate!(int!(0), u32)
                                })
                        }
                        /// DafnyStandardLibraries-rs.dfy(9529,5)
                        pub fn _Empty_q(&self) -> bool {
                            self.beg().clone() == self.end().clone()
                        }
                        /// Returns a borrow of the field s
                        pub fn s(&self) -> &Sequence<u8> {
                            match self {
                                View_::View{s, beg, end, } => s,
                            }
                        }
                        /// Returns a borrow of the field beg
                        pub fn beg(&self) -> &u32 {
                            match self {
                                View_::View{s, beg, end, } => beg,
                            }
                        }
                        /// Returns a borrow of the field end
                        pub fn end(&self) -> &u32 {
                            match self {
                                View_::View{s, beg, end, } => end,
                            }
                        }
                    }

                    impl Debug
                        for View_ {
                        fn fmt(&self, f: &mut Formatter) -> Result {
                            DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint
                        for View_ {
                        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                            match self {
                                View_::View{s, beg, end, } => {
                                    write!(_formatter, "Std.JSON.Utils.Views.Core.View__.View(")?;
                                    DafnyPrint::fmt_print(s, _formatter, false)?;
                                    write!(_formatter, ", ")?;
                                    DafnyPrint::fmt_print(beg, _formatter, false)?;
                                    write!(_formatter, ", ")?;
                                    DafnyPrint::fmt_print(end, _formatter, false)?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                },
                            }
                        }
                    }

                    impl PartialEq
                        for View_ {
                        fn eq(&self, other: &Self) -> bool {
                            match (
                                    self,
                                    other
                                ) {
                                (View_::View{s, beg, end, }, View_::View{s: _2_s, beg: _2_beg, end: _2_end, }) => {
                                    s == _2_s && beg == _2_beg && end == _2_end
                                },
                                _ => {
                                    false
                                },
                            }
                        }
                    }

                    impl Eq
                        for View_ {}

                    impl Hash
                        for View_ {
                        fn hash<_H: Hasher>(&self, _state: &mut _H) {
                            match self {
                                View_::View{s, beg, end, } => {
                                    Hash::hash(s, _state);
                                    Hash::hash(beg, _state);
                                    Hash::hash(end, _state)
                                },
                            }
                        }
                    }

                    impl AsRef<View_>
                        for View_ {
                        fn as_ref(&self) -> &Self {
                            self
                        }
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(9632,1)
                pub mod Writers {
                    pub use ::std::rc::Rc;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use ::dafny_runtime::_System::nat;
                    pub use ::dafny_runtime::int;
                    pub use crate::Std::JSON::Utils::Views::Writers::Chain::Empty;
                    pub use crate::Std::JSON::Utils::Views::Core::View_;
                    pub use ::std::convert::AsRef;
                    pub use ::dafny_runtime::Sequence;
                    pub use ::dafny_runtime::seq;
                    pub use ::dafny_runtime::Object;
                    pub use ::std::fmt::Debug;
                    pub use ::std::fmt::Formatter;
                    pub use ::std::fmt::Result;
                    pub use ::dafny_runtime::DafnyPrint;
                    pub use ::std::cmp::PartialEq;
                    pub use ::std::cmp::Eq;
                    pub use ::std::hash::Hash;
                    pub use ::std::hash::Hasher;
                    pub use ::dafny_runtime::truncate;
                    pub use ::dafny_runtime::MaybePlacebo;
                    pub use ::std::mem::MaybeUninit;
                    pub use ::dafny_runtime::array;
                    pub use ::dafny_runtime::DafnyUsize;
                    pub use ::dafny_runtime::integer_range;
                    pub use ::dafny_runtime::rd;

                    /// DafnyStandardLibraries-rs.dfy(9637,3)
                    #[derive(Clone)]
                    pub enum Chain {
                        Empty {},
                        Chain {
                            previous: Rc<crate::Std::JSON::Utils::Views::Writers::Chain>,
                            v: View
                        }
                    }

                    impl Chain {
                        /// DafnyStandardLibraries-rs.dfy(9638,5)
                        pub fn Length(&self) -> nat {
                            let mut _accumulator: nat = int!(0);
                            let mut _this = Rc::new(self.clone());
                            'TAIL_CALL_START: loop {
                                if matches!((&_this).as_ref(), Empty{ .. }) {
                                    return int!(0) + _accumulator.clone();
                                } else {
                                    _accumulator = int!(View_::Length(AsRef::as_ref(_this.v()))) + _accumulator.clone();
                                    let mut _in0: Rc<crate::Std::JSON::Utils::Views::Writers::Chain> = _this.previous().clone();
                                    _this = _in0.clone();
                                    continue 'TAIL_CALL_START;
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9646,5)
                        pub fn Count(&self) -> nat {
                            let mut _accumulator: nat = int!(0);
                            let mut _this = Rc::new(self.clone());
                            'TAIL_CALL_START: loop {
                                if matches!((&_this).as_ref(), Empty{ .. }) {
                                    return int!(0) + _accumulator.clone();
                                } else {
                                    _accumulator = int!(1) + _accumulator.clone();
                                    let mut _in0: Rc<crate::Std::JSON::Utils::Views::Writers::Chain> = _this.previous().clone();
                                    _this = _in0.clone();
                                    continue 'TAIL_CALL_START;
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9654,5)
                        pub fn Bytes(&self) -> Sequence<u8> {
                            let mut _accumulator: Sequence<u8> = seq![] as Sequence<u8>;
                            let mut _this = Rc::new(self.clone());
                            'TAIL_CALL_START: loop {
                                if matches!((&_this).as_ref(), Empty{ .. }) {
                                    return (seq![] as Sequence<u8>).concat(&_accumulator);
                                } else {
                                    _accumulator = View_::Bytes(AsRef::as_ref(_this.v())).concat(&_accumulator);
                                    let mut _in0: Rc<crate::Std::JSON::Utils::Views::Writers::Chain> = _this.previous().clone();
                                    _this = _in0.clone();
                                    continue 'TAIL_CALL_START;
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9663,5)
                        pub fn Append(&self, _v_k: &View) -> Rc<crate::Std::JSON::Utils::Views::Writers::Chain> {
                            if matches!((&Rc::new(self.clone())).as_ref(), crate::Std::JSON::Utils::Views::Writers::Chain::Chain{ .. }) && crate::Std::JSON::Utils::Views::Core::_default::Adjacent(self.v(), _v_k) {
                                Rc::new(crate::Std::JSON::Utils::Views::Writers::Chain::Chain {
                                        previous: self.previous().clone(),
                                        v: crate::Std::JSON::Utils::Views::Core::_default::Merge(self.v(), _v_k)
                                    })
                            } else {
                                Rc::new(crate::Std::JSON::Utils::Views::Writers::Chain::Chain {
                                        previous: Rc::new(self.clone()),
                                        v: _v_k.clone()
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9672,5)
                        pub fn CopyTo(&self, dest: &Object<[u8]>, end: u32) -> () {
                            let mut _this = Rc::new(self.clone());
                            let mut _r0 = dest.clone();
                            let mut _r1 = end;
                            'TAIL_CALL_START: loop {
                                let dest = _r0;
                                let end = _r1;
                                if matches!((&_this).as_ref(), crate::Std::JSON::Utils::Views::Writers::Chain::Chain{ .. }) {
                                    let mut end: u32 = end - View_::Length(AsRef::as_ref(_this.v()));
                                    View_::CopyTo(AsRef::as_ref(_this.v()), &dest, end);
                                    let mut _in0: Rc<crate::Std::JSON::Utils::Views::Writers::Chain> = _this.previous().clone();
                                    let mut _in1: Object<[u8]> = dest.clone();
                                    let mut _in2: u32 = end;
                                    _this = _in0.clone();
                                    _r0 = _in1.clone();
                                    _r1 = _in2;
                                    continue 'TAIL_CALL_START;
                                };
                                return ();
                            }
                        }
                        /// Gets the field previous for all enum members which have it
                        pub fn previous(&self) -> &Rc<crate::Std::JSON::Utils::Views::Writers::Chain> {
                            match self {
                                Chain::Empty{} => panic!("field does not exist on this variant"),
                                Chain::Chain{previous, v, } => previous,
                            }
                        }
                        /// Gets the field v for all enum members which have it
                        pub fn v(&self) -> &View {
                            match self {
                                Chain::Empty{} => panic!("field does not exist on this variant"),
                                Chain::Chain{previous, v, } => v,
                            }
                        }
                    }

                    impl Debug
                        for Chain {
                        fn fmt(&self, f: &mut Formatter) -> Result {
                            DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint
                        for Chain {
                        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                            match self {
                                Chain::Empty{} => {
                                    write!(_formatter, "Std.JSON.Utils.Views.Writers.Chain.Empty")?;
                                    Ok(())
                                },
                                Chain::Chain{previous, v, } => {
                                    write!(_formatter, "Std.JSON.Utils.Views.Writers.Chain.Chain(")?;
                                    DafnyPrint::fmt_print(previous, _formatter, false)?;
                                    write!(_formatter, ", ")?;
                                    DafnyPrint::fmt_print(v, _formatter, false)?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                },
                            }
                        }
                    }

                    impl PartialEq
                        for Chain {
                        fn eq(&self, other: &Self) -> bool {
                            match (
                                    self,
                                    other
                                ) {
                                (Chain::Empty{}, Chain::Empty{}) => {
                                    true
                                },
                                (Chain::Chain{previous, v, }, Chain::Chain{previous: _2_previous, v: _2_v, }) => {
                                    previous == _2_previous && v == _2_v
                                },
                                _ => {
                                    false
                                },
                            }
                        }
                    }

                    impl Eq
                        for Chain {}

                    impl Hash
                        for Chain {
                        fn hash<_H: Hasher>(&self, _state: &mut _H) {
                            match self {
                                Chain::Empty{} => {
                                    
                                },
                                Chain::Chain{previous, v, } => {
                                    Hash::hash(previous, _state);
                                    Hash::hash(v, _state)
                                },
                            }
                        }
                    }

                    impl AsRef<Chain>
                        for Chain {
                        fn as_ref(&self) -> &Self {
                            self
                        }
                    }

                    /// DafnyStandardLibraries-rs.dfy(9686,3)
                    pub type Writer = Rc<crate::Std::JSON::Utils::Views::Writers::Writer_>;

                    /// An element of Writer
                    pub fn __init_Writer() -> Rc<crate::Std::JSON::Utils::Views::Writers::Writer_> {
                        Rc::new(crate::Std::JSON::Utils::Views::Writers::Writer_::Writer {
                                length: truncate!(int!(0), u32),
                                chain: Rc::new(crate::Std::JSON::Utils::Views::Writers::Chain::Empty {})
                            })
                    }

                    /// DafnyStandardLibraries-rs.dfy(9690,3)
                    #[derive(Clone)]
                    pub enum Writer_ {
                        Writer {
                            length: u32,
                            chain: Rc<crate::Std::JSON::Utils::Views::Writers::Chain>
                        }
                    }

                    impl Writer_ {
                        /// DafnyStandardLibraries-rs.dfy(9702,5)
                        pub fn Bytes(&self) -> Sequence<u8> {
                            self.chain().Bytes()
                        }
                        /// DafnyStandardLibraries-rs.dfy(9708,5)
                        pub fn SaturatedAddU32(a: u32, b: u32) -> u32 {
                            if !(crate::Std::BoundedInts::_default::UINT32_MAX() - b < a) {
                                a + b
                            } else {
                                crate::Std::BoundedInts::_default::UINT32_MAX()
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9716,5)
                        pub fn Append(&self, _v_k: &View) -> crate::Std::JSON::Utils::Views::Writers::Writer {
                            Rc::new(crate::Std::JSON::Utils::Views::Writers::Writer_::Writer {
                                    length: crate::Std::JSON::Utils::Views::Writers::Writer_::SaturatedAddU32(self.length().clone(), View_::Length(AsRef::as_ref(_v_k))),
                                    chain: self.chain().Append(_v_k)
                                })
                        }
                        /// DafnyStandardLibraries-rs.dfy(9724,5)
                        pub fn Then(&self, r#fn: &Rc<dyn ::std::ops::Fn(&crate::Std::JSON::Utils::Views::Writers::Writer) -> crate::Std::JSON::Utils::Views::Writers::Writer>) -> crate::Std::JSON::Utils::Views::Writers::Writer {
                            r#fn(&Rc::new(self.clone()))
                        }
                        /// DafnyStandardLibraries-rs.dfy(9732,5)
                        pub fn CopyTo(&self, dest: &Object<[u8]>) -> () {
                            self.chain().CopyTo(dest, self.length().clone());
                            return ();
                        }
                        /// DafnyStandardLibraries-rs.dfy(9743,5)
                        pub fn ToArray(&self) -> Object<[u8]> {
                            let mut bs = MaybePlacebo::<Object<[u8]>>::new();
                            let mut _init0: Rc<dyn ::std::ops::Fn(&nat) -> u8> = {
                                    Rc::new(move |i: &nat| -> u8{
            truncate!(int!(0), u8)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                };
                            let mut _nw0: Object<[MaybeUninit<u8>]> = array::placebos_usize_object::<u8>(DafnyUsize::into_usize(self.length().clone()));
                            for __i0_0 in integer_range(truncate!(int!(0), usize), rd!(_nw0.clone()).len()) {
                                {
                                    let __idx0 = DafnyUsize::into_usize(__i0_0.clone());
                                    ::dafny_runtime::md!(_nw0)[__idx0] = MaybeUninit::new((&_init0)(&int!(__i0_0.clone())));
                                }
                            }
                            bs = MaybePlacebo::from(array::construct_object(_nw0.clone()));
                            self.CopyTo(&bs.read());
                            return bs.read();
                        }
                        /// DafnyStandardLibraries-rs.dfy(9691,5)
                        pub fn Empty() -> crate::Std::JSON::Utils::Views::Writers::Writer {
                            Rc::new(crate::Std::JSON::Utils::Views::Writers::Writer_::Writer {
                                    length: truncate!(int!(0), u32),
                                    chain: Rc::new(crate::Std::JSON::Utils::Views::Writers::Chain::Empty {})
                                })
                        }
                        /// DafnyStandardLibraries-rs.dfy(9693,5)
                        pub fn _Unsaturated_q(&self) -> bool {
                            !(self.length().clone() == crate::Std::BoundedInts::_default::UINT32_MAX())
                        }
                        /// DafnyStandardLibraries-rs.dfy(9692,5)
                        pub fn _Empty_q(&self) -> bool {
                            matches!(self.chain().as_ref(), Empty{ .. })
                        }
                        /// Returns a borrow of the field length
                        pub fn length(&self) -> &u32 {
                            match self {
                                Writer_::Writer{length, chain, } => length,
                            }
                        }
                        /// Returns a borrow of the field chain
                        pub fn chain(&self) -> &Rc<crate::Std::JSON::Utils::Views::Writers::Chain> {
                            match self {
                                Writer_::Writer{length, chain, } => chain,
                            }
                        }
                    }

                    impl Debug
                        for Writer_ {
                        fn fmt(&self, f: &mut Formatter) -> Result {
                            DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint
                        for Writer_ {
                        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                            match self {
                                Writer_::Writer{length, chain, } => {
                                    write!(_formatter, "Std.JSON.Utils.Views.Writers.Writer__.Writer(")?;
                                    DafnyPrint::fmt_print(length, _formatter, false)?;
                                    write!(_formatter, ", ")?;
                                    DafnyPrint::fmt_print(chain, _formatter, false)?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                },
                            }
                        }
                    }

                    impl PartialEq
                        for Writer_ {
                        fn eq(&self, other: &Self) -> bool {
                            match (
                                    self,
                                    other
                                ) {
                                (Writer_::Writer{length, chain, }, Writer_::Writer{length: _2_length, chain: _2_chain, }) => {
                                    length == _2_length && chain == _2_chain
                                },
                                _ => {
                                    false
                                },
                            }
                        }
                    }

                    impl Eq
                        for Writer_ {}

                    impl Hash
                        for Writer_ {
                        fn hash<_H: Hasher>(&self, _state: &mut _H) {
                            match self {
                                Writer_::Writer{length, chain, } => {
                                    Hash::hash(length, _state);
                                    Hash::hash(chain, _state)
                                },
                            }
                        }
                    }

                    impl AsRef<Writer_>
                        for Writer_ {
                        fn as_ref(&self) -> &Self {
                            self
                        }
                    }
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(9755,1)
        pub mod Values {
            pub use ::dafny_runtime::DafnyInt;
            pub use ::std::rc::Rc;
            pub use ::dafny_runtime::int;
            pub use ::std::fmt::Debug;
            pub use ::std::fmt::Formatter;
            pub use ::std::fmt::Result;
            pub use ::dafny_runtime::DafnyPrint;
            pub use ::std::cmp::PartialEq;
            pub use ::std::cmp::Eq;
            pub use ::std::hash::Hash;
            pub use ::std::hash::Hasher;
            pub use ::std::convert::AsRef;
            pub use ::dafny_runtime::Sequence;
            pub use ::dafny_runtime::DafnyChar;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(9756,3)
                pub fn Int(n: &DafnyInt) -> Rc<crate::Std::JSON::Values::Decimal> {
                    Rc::new(crate::Std::JSON::Values::Decimal::Decimal {
                            n: n.clone(),
                            e10: int!(0)
                        })
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9761,3)
            #[derive(Clone)]
            pub enum Decimal {
                Decimal {
                    n: DafnyInt,
                    e10: DafnyInt
                }
            }

            impl Decimal {
                /// Returns a borrow of the field n
                pub fn n(&self) -> &DafnyInt {
                    match self {
                        Decimal::Decimal{n, e10, } => n,
                    }
                }
                /// Returns a borrow of the field e10
                pub fn e10(&self) -> &DafnyInt {
                    match self {
                        Decimal::Decimal{n, e10, } => e10,
                    }
                }
            }

            impl Debug
                for Decimal {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for Decimal {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        Decimal::Decimal{n, e10, } => {
                            write!(_formatter, "Std.JSON.Values.Decimal.Decimal(")?;
                            DafnyPrint::fmt_print(n, _formatter, false)?;
                            write!(_formatter, ", ")?;
                            DafnyPrint::fmt_print(e10, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for Decimal {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (Decimal::Decimal{n, e10, }, Decimal::Decimal{n: _2_n, e10: _2_e10, }) => {
                            n == _2_n && e10 == _2_e10
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for Decimal {}

            impl Hash
                for Decimal {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        Decimal::Decimal{n, e10, } => {
                            Hash::hash(n, _state);
                            Hash::hash(e10, _state)
                        },
                    }
                }
            }

            impl AsRef<Decimal>
                for Decimal {
                fn as_ref(&self) -> &Self {
                    self
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9763,3)
            #[derive(Clone)]
            pub enum JSON {
                Null {},
                Bool {
                    b: bool
                },
                String {
                    str: Sequence<DafnyChar>
                },
                Number {
                    num: Rc<crate::Std::JSON::Values::Decimal>
                },
                Object {
                    obj: Sequence<(Sequence<DafnyChar>, Rc<crate::Std::JSON::Values::JSON>)>
                },
                Array {
                    arr: Sequence<Rc<crate::Std::JSON::Values::JSON>>
                }
            }

            impl JSON {
                /// Gets the field b for all enum members which have it
                pub fn b(&self) -> &bool {
                    match self {
                        JSON::Null{} => panic!("field does not exist on this variant"),
                        JSON::Bool{b, } => b,
                        JSON::String{str, } => panic!("field does not exist on this variant"),
                        JSON::Number{num, } => panic!("field does not exist on this variant"),
                        JSON::Object{obj, } => panic!("field does not exist on this variant"),
                        JSON::Array{arr, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field str for all enum members which have it
                pub fn str(&self) -> &Sequence<DafnyChar> {
                    match self {
                        JSON::Null{} => panic!("field does not exist on this variant"),
                        JSON::Bool{b, } => panic!("field does not exist on this variant"),
                        JSON::String{str, } => str,
                        JSON::Number{num, } => panic!("field does not exist on this variant"),
                        JSON::Object{obj, } => panic!("field does not exist on this variant"),
                        JSON::Array{arr, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field num for all enum members which have it
                pub fn num(&self) -> &Rc<crate::Std::JSON::Values::Decimal> {
                    match self {
                        JSON::Null{} => panic!("field does not exist on this variant"),
                        JSON::Bool{b, } => panic!("field does not exist on this variant"),
                        JSON::String{str, } => panic!("field does not exist on this variant"),
                        JSON::Number{num, } => num,
                        JSON::Object{obj, } => panic!("field does not exist on this variant"),
                        JSON::Array{arr, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field obj for all enum members which have it
                pub fn obj(&self) -> &Sequence<(Sequence<DafnyChar>, Rc<crate::Std::JSON::Values::JSON>)> {
                    match self {
                        JSON::Null{} => panic!("field does not exist on this variant"),
                        JSON::Bool{b, } => panic!("field does not exist on this variant"),
                        JSON::String{str, } => panic!("field does not exist on this variant"),
                        JSON::Number{num, } => panic!("field does not exist on this variant"),
                        JSON::Object{obj, } => obj,
                        JSON::Array{arr, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field arr for all enum members which have it
                pub fn arr(&self) -> &Sequence<Rc<crate::Std::JSON::Values::JSON>> {
                    match self {
                        JSON::Null{} => panic!("field does not exist on this variant"),
                        JSON::Bool{b, } => panic!("field does not exist on this variant"),
                        JSON::String{str, } => panic!("field does not exist on this variant"),
                        JSON::Number{num, } => panic!("field does not exist on this variant"),
                        JSON::Object{obj, } => panic!("field does not exist on this variant"),
                        JSON::Array{arr, } => arr,
                    }
                }
            }

            impl Debug
                for JSON {
                fn fmt(&self, f: &mut Formatter) -> Result {
                    DafnyPrint::fmt_print(self, f, true)
                }
            }

            impl DafnyPrint
                for JSON {
                fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
                    match self {
                        JSON::Null{} => {
                            write!(_formatter, "Std.JSON.Values.JSON.Null")?;
                            Ok(())
                        },
                        JSON::Bool{b, } => {
                            write!(_formatter, "Std.JSON.Values.JSON.Bool(")?;
                            DafnyPrint::fmt_print(b, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        JSON::String{str, } => {
                            write!(_formatter, "Std.JSON.Values.JSON.String(")?;
                            DafnyPrint::fmt_print(str, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        JSON::Number{num, } => {
                            write!(_formatter, "Std.JSON.Values.JSON.Number(")?;
                            DafnyPrint::fmt_print(num, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        JSON::Object{obj, } => {
                            write!(_formatter, "Std.JSON.Values.JSON.Object(")?;
                            DafnyPrint::fmt_print(obj, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        JSON::Array{arr, } => {
                            write!(_formatter, "Std.JSON.Values.JSON.Array(")?;
                            DafnyPrint::fmt_print(arr, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                    }
                }
            }

            impl PartialEq
                for JSON {
                fn eq(&self, other: &Self) -> bool {
                    match (
                            self,
                            other
                        ) {
                        (JSON::Null{}, JSON::Null{}) => {
                            true
                        },
                        (JSON::Bool{b, }, JSON::Bool{b: _2_b, }) => {
                            b == _2_b
                        },
                        (JSON::String{str, }, JSON::String{str: _2_str, }) => {
                            str == _2_str
                        },
                        (JSON::Number{num, }, JSON::Number{num: _2_num, }) => {
                            num == _2_num
                        },
                        (JSON::Object{obj, }, JSON::Object{obj: _2_obj, }) => {
                            obj == _2_obj
                        },
                        (JSON::Array{arr, }, JSON::Array{arr: _2_arr, }) => {
                            arr == _2_arr
                        },
                        _ => {
                            false
                        },
                    }
                }
            }

            impl Eq
                for JSON {}

            impl Hash
                for JSON {
                fn hash<_H: Hasher>(&self, _state: &mut _H) {
                    match self {
                        JSON::Null{} => {
                            
                        },
                        JSON::Bool{b, } => {
                            Hash::hash(b, _state)
                        },
                        JSON::String{str, } => {
                            Hash::hash(str, _state)
                        },
                        JSON::Number{num, } => {
                            Hash::hash(num, _state)
                        },
                        JSON::Object{obj, } => {
                            Hash::hash(obj, _state)
                        },
                        JSON::Array{arr, } => {
                            Hash::hash(arr, _state)
                        },
                    }
                }
            }

            impl AsRef<JSON>
                for JSON {
                fn as_ref(&self) -> &Self {
                    self
                }
            }
        }

        pub mod ZeroCopy {
            /// DafnyStandardLibraries-rs.dfy(9766,1)
            pub mod API {
                pub use ::std::rc::Rc;
                pub use crate::Std::JSON::Grammar::Structural;
                pub use crate::Std::JSON::Grammar::Value;
                pub use crate::Std::Wrappers::Result;
                pub use ::dafny_runtime::Sequence;
                pub use crate::Std::JSON::Errors::SerializationError;
                pub use crate::Std::JSON::Utils::Views::Writers::Writer_;
                pub use ::std::convert::AsRef;
                pub use ::dafny_runtime::Object;
                pub use crate::Std::JSON::Errors::DeserializationError;

                pub struct _default {}

                impl _default {
                    /// DafnyStandardLibraries-rs.dfy(9767,3)
                    pub fn Serialize(js: &Rc<Structural<Rc<Value>>>) -> Rc<Result<Sequence<u8>, Rc<SerializationError>>> {
                        Rc::new(Result::Success::<Sequence<u8>, Rc<SerializationError>> {
                                value: Writer_::Bytes(AsRef::as_ref(&crate::Std::JSON::ZeroCopy::Serializer::_default::Text(js)))
                            })
                    }
                    /// DafnyStandardLibraries-rs.dfy(9773,3)
                    pub fn SerializeAlloc(js: &Rc<Structural<Rc<Value>>>) -> Rc<Result<Object<[u8]>, Rc<SerializationError>>> {
                        let mut bs: Rc<Result<Object<[u8]>, Rc<SerializationError>>>;
                        let mut _out0: Rc<Result<Object<[u8]>, Rc<SerializationError>>>;
                        _out0 = crate::Std::JSON::ZeroCopy::Serializer::_default::Serialize(js);
                        bs = _out0.clone();
                        return bs.clone();
                    }
                    /// DafnyStandardLibraries-rs.dfy(9780,3)
                    pub fn SerializeInto(js: &Rc<Structural<Rc<Value>>>, bs: &Object<[u8]>) -> Rc<Result<u32, Rc<SerializationError>>> {
                        let mut len: Rc<Result<u32, Rc<SerializationError>>>;
                        let mut _out0: Rc<Result<u32, Rc<SerializationError>>>;
                        _out0 = crate::Std::JSON::ZeroCopy::Serializer::_default::SerializeTo(js, bs);
                        len = _out0.clone();
                        return len.clone();
                    }
                    /// DafnyStandardLibraries-rs.dfy(9790,3)
                    pub fn Deserialize(bs: &Sequence<u8>) -> Rc<Result<Rc<Structural<Rc<Value>>>, Rc<DeserializationError>>> {
                        crate::Std::JSON::ZeroCopy::Deserializer::API::_default::OfBytes(bs)
                    }
                }
            }

            /// DafnyStandardLibraries-rs.dfy(9811,1)
            pub mod Deserializer {
                /// DafnyStandardLibraries-rs.dfy(10250,3)
                pub mod API {
                    pub use ::std::rc::Rc;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError::EOF;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError::ExpectingByte;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError::ExpectingAnyByte;
                    pub use ::dafny_runtime::Sequence;
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Grammar::Structural;
                    pub use crate::Std::JSON::Grammar::Value;
                    pub use crate::Std::JSON::Utils::Parsers::Parser_;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor_;
                    pub use crate::Std::Wrappers::OutcomeResult;
                    pub use crate::Std::JSON::Utils::Views::Core::View_;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(10251,5)
                        pub fn LiftCursorError(err: &Rc<CursorError<Rc<DeserializationError>>>) -> Rc<DeserializationError> {
                            let mut _source0: Rc<CursorError<Rc<DeserializationError>>> = err.clone();
                            if matches!((&_source0).as_ref(), EOF{ .. }) {
                                Rc::new(DeserializationError::ReachedEOF {})
                            } else {
                                if matches!((&_source0).as_ref(), ExpectingByte{ .. }) {
                                    let mut ___mcc_h0: u8 = _source0.expected().clone();
                                    let mut ___mcc_h1: i16 = _source0.b().clone();
                                    let mut b: i16 = ___mcc_h1;
                                    let mut expected: u8 = ___mcc_h0;
                                    Rc::new(DeserializationError::ExpectingByte {
                                            expected: expected,
                                            b: b
                                        })
                                } else {
                                    if matches!((&_source0).as_ref(), ExpectingAnyByte{ .. }) {
                                        let mut ___mcc_h2: Sequence<u8> = _source0.expected_sq().clone();
                                        let mut ___mcc_h3: i16 = _source0.b().clone();
                                        let mut b: i16 = ___mcc_h3;
                                        let mut expected_sq: Sequence<u8> = ___mcc_h2.clone();
                                        Rc::new(DeserializationError::ExpectingAnyByte {
                                                expected_sq: expected_sq.clone(),
                                                b: b
                                            })
                                    } else {
                                        let mut ___mcc_h4: Rc<DeserializationError> = _source0.err().clone();
                                        let mut err: Rc<DeserializationError> = ___mcc_h4.clone();
                                        err.clone()
                                    }
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10264,5)
                        pub fn JSON(cs: &FreshCursor) -> Rc<Result<Rc<Split<Rc<Structural<Rc<Value>>>>>, Rc<DeserializationError>>> {
                            crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::Structural::<Rc<Value>>(cs, &Rc::new(Parser_::Parser::<Rc<Value>, Rc<DeserializationError>> {
                                        r#fn: Rc::new(move |x0: &FreshCursor| crate::Std::JSON::ZeroCopy::Deserializer::Values::_default::Value(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                    })).MapFailure::<Rc<DeserializationError>>(&(Rc::new(move |x0: &Rc<CursorError<Rc<DeserializationError>>>| crate::Std::JSON::ZeroCopy::Deserializer::API::_default::LiftCursorError(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>))
                        }
                        /// DafnyStandardLibraries-rs.dfy(10270,5)
                        pub fn Text(v: &View) -> Rc<Result<Rc<Structural<Rc<Value>>>, Rc<DeserializationError>>> {
                            let mut valueOrError0: Rc<Result<Rc<Split<Rc<Structural<Rc<Value>>>>>, Rc<DeserializationError>>> = crate::Std::JSON::ZeroCopy::Deserializer::API::_default::JSON(&Cursor_::OfView(v));
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Structural<Rc<Value>>>>()
                            } else {
                                let mut __let_tmp_rhs0: Rc<Split<Rc<Structural<Rc<Value>>>>> = valueOrError0.Extract();
                                let mut text: Rc<Structural<Rc<Value>>> = __let_tmp_rhs0.t().clone();
                                let mut cs: FreshCursor = __let_tmp_rhs0.cs().clone();
                                let mut valueOrError1: Rc<OutcomeResult<Rc<DeserializationError>>> = crate::Std::Wrappers::_default::Need::<Rc<DeserializationError>>(cs._EOF_q(), &Rc::new(DeserializationError::ExpectingEOF {}));
                                if valueOrError1.IsFailure() {
                                    valueOrError1.PropagateFailure::<Rc<Structural<Rc<Value>>>>()
                                } else {
                                    Rc::new(Result::Success::<Rc<Structural<Rc<Value>>>, Rc<DeserializationError>> {
                                            value: text.clone()
                                        })
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10276,5)
                        pub fn OfBytes(bs: &Sequence<u8>) -> Rc<Result<Rc<Structural<Rc<Value>>>, Rc<DeserializationError>>> {
                            let mut valueOrError0: Rc<OutcomeResult<Rc<DeserializationError>>> = crate::Std::Wrappers::_default::Need::<Rc<DeserializationError>>(bs.cardinality() < crate::Std::BoundedInts::_default::TWO_TO_THE_32(), &Rc::new(DeserializationError::IntOverflow {}));
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Structural<Rc<Value>>>>()
                            } else {
                                crate::Std::JSON::ZeroCopy::Deserializer::API::_default::Text(&View_::OfBytes(bs))
                            }
                        }
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(10640,3)
                pub mod ArrayParams {
                    pub use ::std::rc::Rc;
                    pub use crate::Std::JSON::Grammar::Value;
                    pub use ::dafny_runtime::Sequence;
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use crate::Std::JSON::ZeroCopy::Deserializer::Core::ValueParser;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use ::dafny_runtime::DafnyChar;
                    pub use ::std::primitive::char;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(10644,5)
                        pub fn ElementSpec(t: &Rc<Value>) -> Sequence<u8> {
                            crate::Std::JSON::ConcreteSyntax::Spec::_default::Value(t)
                        }
                        /// DafnyStandardLibraries-rs.dfy(10649,5)
                        pub fn Element(cs: &FreshCursor, json: &ValueParser) -> Rc<Result<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            json.r#fn()(cs)
                        }
                        /// DafnyStandardLibraries-rs.dfy(10641,5)
                        pub fn OPEN() -> u8 {
                            DafnyChar(char::from_u32(91).unwrap()).0 as u8
                        }
                        /// DafnyStandardLibraries-rs.dfy(10642,5)
                        pub fn CLOSE() -> u8 {
                            DafnyChar(char::from_u32(93).unwrap()).0 as u8
                        }
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(10661,3)
                pub mod Arrays {
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use crate::Std::JSON::ZeroCopy::Deserializer::Core::ValueParser;
                    pub use ::std::rc::Rc;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Grammar::Bracketed;
                    pub use crate::Std::JSON::Grammar::jlbracket;
                    pub use crate::Std::JSON::Grammar::Value;
                    pub use crate::Std::JSON::Grammar::jcomma;
                    pub use crate::Std::JSON::Grammar::jrbracket;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor_;
                    pub use ::std::convert::AsRef;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use crate::Std::JSON::Grammar::Structural;
                    pub use ::dafny_runtime::Sequence;
                    pub use crate::Std::JSON::Grammar::Suffixed;
                    pub use crate::Std::JSON::Grammar::Maybe;
                    pub use ::dafny_runtime::seq;
                    pub use crate::Std::JSON::ZeroCopy::Deserializer::Core::jopt;
                    pub use crate::Std::JSON::Utils::Views::Core::View_;
                    pub use ::dafny_runtime::truncate;
                    pub use ::dafny_runtime::int;
                    pub use crate::Std::JSON::Utils::Parsers::Parser_;
                    pub use ::dafny_runtime::DafnyChar;
                    pub use ::std::primitive::char;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(10677,5)
                        pub fn Array(cs: &FreshCursor, json: &ValueParser) -> Rc<Result<Rc<Split<Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::Bracketed(cs, json);
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>>()
                            } else {
                                let mut sp: Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>> = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: sp.clone()
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9944,5)
                        pub fn Open(cs: &FreshCursor) -> Rc<Result<Rc<Split<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> = Cursor_::AssertByte::<Rc<DeserializationError>>(AsRef::as_ref(cs), crate::Std::JSON::ZeroCopy::Deserializer::ArrayParams::_default::OPEN());
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<View>>>()
                            } else {
                                let mut cs: Cursor = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Cursor_::Split(AsRef::as_ref(&cs))
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9950,5)
                        pub fn Close(cs: &FreshCursor) -> Rc<Result<Rc<Split<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> = Cursor_::AssertByte::<Rc<DeserializationError>>(AsRef::as_ref(cs), crate::Std::JSON::ZeroCopy::Deserializer::ArrayParams::_default::CLOSE());
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<View>>>()
                            } else {
                                let mut cs: Cursor = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Cursor_::Split(AsRef::as_ref(&cs))
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9956,5)
                        pub fn BracketedFromParts(open: &Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen>>>>, elems: &Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>>, close: &Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>) -> Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>> {
                            let mut sp: Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>> = Rc::new(Split::SP::<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>> {
                                        t: Rc::new(Bracketed::Bracketed::<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose> {
                                                    l: open.t().clone(),
                                                    data: elems.t().clone(),
                                                    r: close.t().clone()
                                                }),
                                        cs: close.cs().clone()
                                    });
                            sp.clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(9989,5)
                        pub fn AppendWithSuffix(elems: &Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>>, elem: &Rc<Split<Rc<Value>>>, sep: &Rc<Split<Rc<Structural<jcomma>>>>) -> Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>> {
                            let mut suffixed: Rc<Suffixed<Rc<Value>, jcomma>> = Rc::new(Suffixed::Suffixed::<Rc<Value>, jcomma> {
                                        t: elem.t().clone(),
                                        suffix: Rc::new(Maybe::NonEmpty::<Rc<Structural<jcomma>>> {
                                                    t: sep.t().clone()
                                                })
                                    });
                            let mut _elems_k: Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>> = Rc::new(Split::SP::<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>> {
                                        t: elems.t().concat(&seq![suffixed.clone()]),
                                        cs: sep.cs().clone()
                                    });
                            _elems_k.clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(10039,5)
                        pub fn AppendLast(elems: &Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>>, elem: &Rc<Split<Rc<Value>>>, sep: &Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>) -> Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>> {
                            let mut suffixed: Rc<Suffixed<Rc<Value>, jcomma>> = Rc::new(Suffixed::Suffixed::<Rc<Value>, jcomma> {
                                        t: elem.t().clone(),
                                        suffix: Rc::new(Maybe::Empty::<Rc<Structural<jcomma>>> {})
                                    });
                            let mut _elems_k: Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>> = Rc::new(Split::SP::<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>> {
                                        t: elems.t().concat(&seq![suffixed.clone()]),
                                        cs: elem.cs().clone()
                                    });
                            _elems_k.clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(10085,5)
                        pub fn Elements(json: &ValueParser, open: &Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen>>>>, elems: &Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>>) -> Rc<Result<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut _r0 = json.clone();
                            let mut _r1 = open.clone();
                            let mut _r2 = elems.clone();
                            'TAIL_CALL_START: loop {
                                let json = _r0;
                                let open = _r1;
                                let elems = _r2;
                                let mut valueOrError0: Rc<Result<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::ArrayParams::_default::Element(elems.cs(), &json);
                                if valueOrError0.IsFailure() {
                                    return valueOrError0.PropagateFailure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>>();
                                } else {
                                    let mut elem: Rc<Split<Rc<Value>>> = valueOrError0.Extract();
                                    if elem.cs()._EOF_q() {
                                        return Rc::new(Result::Failure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                    error: Rc::new(CursorError::EOF::<Rc<DeserializationError>> {})
                                                });
                                    } else {
                                        let mut sep: Rc<Split<Rc<Structural<jopt>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::TryStructural(elem.cs());
                                        let mut s0: i16 = View_::Peek(AsRef::as_ref(sep.t().t()));
                                        if s0 == crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::SEPARATOR() as i16 && View_::Length(AsRef::as_ref(sep.t().t())) == truncate!(int!(1), u32) {
                                            let mut sep: Rc<Split<Rc<Structural<jcomma>>>> = sep.clone();
                                            let mut elems: Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::AppendWithSuffix(&elems, &elem, &sep);
                                            let mut _in0: ValueParser = json.clone();
                                            let mut _in1: Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen>>>> = open.clone();
                                            let mut _in2: Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>> = elems.clone();
                                            _r0 = _in0.clone();
                                            _r1 = _in1.clone();
                                            _r2 = _in2.clone();
                                            continue 'TAIL_CALL_START;
                                        } else {
                                            if s0 == crate::Std::JSON::ZeroCopy::Deserializer::ArrayParams::_default::CLOSE() as i16 && View_::Length(AsRef::as_ref(sep.t().t())) == truncate!(int!(1), u32) {
                                                let mut sep: Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>> = sep.clone();
                                                let mut _elems_k: Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::AppendLast(&elems, &elem, &sep);
                                                let mut bracketed: Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::BracketedFromParts(&open, &_elems_k, &sep);
                                                return Rc::new(Result::Success::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                            value: bracketed.clone()
                                                        });
                                            } else {
                                                let mut separator: u8 = crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::SEPARATOR();
                                                let mut pr: Rc<Result<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = Rc::new(Result::Failure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                            error: Rc::new(CursorError::ExpectingAnyByte::<Rc<DeserializationError>> {
                                                                        expected_sq: seq![crate::Std::JSON::ZeroCopy::Deserializer::ArrayParams::_default::CLOSE(), separator],
                                                                        b: s0
                                                                    })
                                                        });
                                                return pr.clone();
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10193,5)
                        pub fn Bracketed(cs: &FreshCursor, json: &ValueParser) -> Rc<Result<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::Structural::<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen>(cs, &Rc::new(Parser_::Parser::<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<DeserializationError>> {
                                            r#fn: Rc::new(move |x0: &FreshCursor| crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::Open(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }));
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>>()
                            } else {
                                let mut open: Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen>>>> = valueOrError0.Extract();
                                let mut elems: Rc<Split<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>>> = Rc::new(Split::SP::<Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>> {
                                            t: seq![] as Sequence<Rc<Suffixed<Rc<Value>, jcomma>>>,
                                            cs: open.cs().clone()
                                        });
                                if Cursor_::Peek(AsRef::as_ref(open.cs())) == crate::Std::JSON::ZeroCopy::Deserializer::ArrayParams::_default::CLOSE() as i16 {
                                    let mut p: Rc<Parser_<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose, Rc<DeserializationError>>> = Rc::new(Parser_::Parser::<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose, Rc<DeserializationError>> {
                                                r#fn: Rc::new(move |x0: &FreshCursor| crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::Close(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                            });
                                    let mut valueOrError1: Rc<Result<Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::Structural::<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>(open.cs(), &p);
                                    if valueOrError1.IsFailure() {
                                        valueOrError1.PropagateFailure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>>()
                                    } else {
                                        let mut close: Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>> = valueOrError1.Extract();
                                        Rc::new(Result::Success::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen, Rc<Value>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                value: crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::BracketedFromParts(&open, &elems, &close)
                                            })
                                    }
                                } else {
                                    crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::Elements(json, &open, &elems)
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9927,5)
                        pub fn SpecViewOpen() -> Rc<dyn ::std::ops::Fn(&crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jopen) -> Sequence<u8>> {
                            Rc::new(move |x0: &View| crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::SpecView()(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                        /// DafnyStandardLibraries-rs.dfy(9926,5)
                        pub fn SpecViewClose() -> Rc<dyn ::std::ops::Fn(&crate::Std::JSON::ZeroCopy::Deserializer::Arrays::jclose) -> Sequence<u8>> {
                            Rc::new(move |x0: &View| crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::SpecView()(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                        /// DafnyStandardLibraries-rs.dfy(9925,5)
                        pub fn SEPARATOR() -> u8 {
                            DafnyChar(char::from_u32(44).unwrap()).0 as u8
                        }
                    }

                    /// DafnyStandardLibraries-rs.dfy(10237,5)
                    pub type jopen = Rc<View_>;

                    /// An element of jopen
                    pub fn __init_jopen() -> Rc<View_> {
                        View_::OfBytes(&seq![crate::Std::JSON::ZeroCopy::Deserializer::ArrayParams::_default::OPEN()])
                    }

                    /// DafnyStandardLibraries-rs.dfy(10241,5)
                    pub type jclose = Rc<View_>;

                    /// An element of jclose
                    pub fn __init_jclose() -> Rc<View_> {
                        View_::OfBytes(&seq![crate::Std::JSON::ZeroCopy::Deserializer::ArrayParams::_default::CLOSE()])
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(10460,3)
                pub mod Constants {
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use ::dafny_runtime::Sequence;
                    pub use ::std::rc::Rc;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor_;
                    pub use ::std::convert::AsRef;
                    pub use ::dafny_runtime::truncate;
                    pub use ::dafny_runtime::int;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(10461,5)
                        pub fn Constant(cs: &FreshCursor, expected: &Sequence<u8>) -> Rc<Result<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> = Cursor_::AssertBytes::<Rc<DeserializationError>>(AsRef::as_ref(cs), expected, truncate!(int!(0), u32));
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<View>>>()
                            } else {
                                let mut cs: Cursor = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Cursor_::Split(AsRef::as_ref(&cs))
                                    })
                            }
                        }
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(9813,3)
                pub mod Core {
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use ::std::rc::Rc;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Grammar::jchar;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor_;
                    pub use ::std::convert::AsRef;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use crate::Std::JSON::Grammar::jblanks;
                    pub use ::dafny_runtime::MaybePlacebo;
                    pub use ::dafny_runtime::int;
                    pub use ::dafny_runtime::truncate;
                    pub use ::dafny_runtime::DafnyType;
                    pub use crate::Std::JSON::Utils::Parsers::Parser;
                    pub use crate::Std::JSON::Grammar::Structural;
                    pub use ::dafny_runtime::Sequence;
                    pub use crate::Std::JSON::Utils::Views::Core::View_;
                    pub use ::dafny_runtime::seq;
                    pub use crate::Std::JSON::Utils::Parsers::SubParser_;
                    pub use crate::Std::JSON::Grammar::Value;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(9816,5)
                        pub fn Get(cs: &FreshCursor, err: &Rc<DeserializationError>) -> Rc<Result<Rc<Split<jchar>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> = Cursor_::Get::<Rc<DeserializationError>>(AsRef::as_ref(cs), err);
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<View>>>()
                            } else {
                                let mut cs: Cursor = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Cursor_::Split(AsRef::as_ref(&cs))
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9822,5)
                        pub fn WS(cs: &FreshCursor) -> Rc<Split<jblanks>> {
                            let mut sp = MaybePlacebo::<Rc<Split<jblanks>>>::new();
                            let mut _point_k: u32 = cs.point().clone();
                            let mut end: u32 = cs.end().clone();
                            while _point_k < end && crate::Std::JSON::Grammar::_default::_Blank_q(cs.s().get(&int!((&_point_k).clone()))) {
                                _point_k = _point_k + truncate!(int!(1), u32);
                            };
                            sp = MaybePlacebo::from(Rc::new(Cursor_::Cursor {
                                            s: cs.s().clone(),
                                            beg: cs.beg().clone(),
                                            point: _point_k,
                                            end: cs.end().clone()
                                        }).Split());
                            return sp.read();
                        }
                        /// DafnyStandardLibraries-rs.dfy(9841,5)
                        pub fn Structural<_T: DafnyType>(cs: &FreshCursor, parser: &Parser<_T, Rc<DeserializationError>>) -> Rc<Result<Rc<Split<Rc<Structural<_T>>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut __let_tmp_rhs0: Rc<Split<jblanks>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::WS(cs);
                            let mut before: jblanks = __let_tmp_rhs0.t().clone();
                            let mut cs: FreshCursor = __let_tmp_rhs0.cs().clone();
                            let mut valueOrError0: Rc<Result<Rc<Split<_T>>, Rc<CursorError<Rc<DeserializationError>>>>> = parser.r#fn()(&cs);
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<Rc<Structural<_T>>>>>()
                            } else {
                                let mut __let_tmp_rhs1: Rc<Split<_T>> = valueOrError0.Extract();
                                let mut val: _T = __let_tmp_rhs1.t().clone();
                                let mut cs: FreshCursor = __let_tmp_rhs1.cs().clone();
                                let mut __let_tmp_rhs2: Rc<Split<jblanks>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::WS(&cs);
                                let mut after: jblanks = __let_tmp_rhs2.t().clone();
                                let mut cs: FreshCursor = __let_tmp_rhs2.cs().clone();
                                Rc::new(Result::Success::<Rc<Split<Rc<Structural<_T>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Rc::new(Split::SP::<Rc<Structural<_T>>> {
                                                    t: Rc::new(Structural::Structural::<_T> {
                                                                before: before.clone(),
                                                                t: val.clone(),
                                                                after: after.clone()
                                                            }),
                                                    cs: cs.clone()
                                                })
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9849,5)
                        pub fn TryStructural(cs: &FreshCursor) -> Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Core::jopt>>>> {
                            let mut __let_tmp_rhs0: Rc<Split<jblanks>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::WS(cs);
                            let mut before: jblanks = __let_tmp_rhs0.t().clone();
                            let mut cs: FreshCursor = __let_tmp_rhs0.cs().clone();
                            let mut __let_tmp_rhs1: Rc<Split<View>> = Cursor_::Split(AsRef::as_ref(&Cursor_::SkipByte(AsRef::as_ref(&cs))));
                            let mut val: View = __let_tmp_rhs1.t().clone();
                            let mut cs: FreshCursor = __let_tmp_rhs1.cs().clone();
                            let mut __let_tmp_rhs2: Rc<Split<jblanks>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::WS(&cs);
                            let mut after: jblanks = __let_tmp_rhs2.t().clone();
                            let mut cs: FreshCursor = __let_tmp_rhs2.cs().clone();
                            Rc::new(Split::SP::<Rc<Structural<View>>> {
                                    t: Rc::new(Structural::Structural::<View> {
                                                before: before.clone(),
                                                t: val.clone(),
                                                after: after.clone()
                                            }),
                                    cs: cs.clone()
                                })
                        }
                        /// DafnyStandardLibraries-rs.dfy(9814,5)
                        pub fn SpecView() -> Rc<dyn ::std::ops::Fn(&View) -> Sequence<u8>> {
                            {
                                Rc::new(move |v: &View| -> Sequence<u8>{
            crate::Std::JSON::ConcreteSyntax::Spec::_default::View(v)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                            }
                        }
                    }

                    /// DafnyStandardLibraries-rs.dfy(9892,5)
                    pub type jopt = Rc<View_>;

                    /// An element of jopt
                    pub fn __init_jopt() -> Rc<View_> {
                        View_::OfBytes(&(seq![] as Sequence<u8>))
                    }

                    /// DafnyStandardLibraries-rs.dfy(9896,5)
                    pub type ValueParser = Rc<SubParser_<Rc<Value>, Rc<DeserializationError>>>;
                }

                /// DafnyStandardLibraries-rs.dfy(10533,3)
                pub mod Numbers {
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use ::std::rc::Rc;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Grammar::jdigits;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor_;
                    pub use ::std::convert::AsRef;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Grammar::jnum;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use crate::Std::JSON::Grammar::jint;
                    pub use crate::Std::JSON::Grammar::jminus;
                    pub use ::dafny_runtime::DafnyChar;
                    pub use ::std::primitive::char;
                    pub use crate::Std::JSON::Grammar::jsign;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use crate::Std::JSON::Grammar::Maybe;
                    pub use crate::Std::JSON::Grammar::jexp;
                    pub use crate::Std::JSON::Grammar::jfrac;
                    pub use crate::Std::JSON::Grammar::jnumber;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(10534,5)
                        pub fn Digits(cs: &FreshCursor) -> Rc<Split<jdigits>> {
                            Cursor_::Split(AsRef::as_ref(&Cursor_::SkipWhile(AsRef::as_ref(cs), &(Rc::new(move |x0: &u8| crate::Std::JSON::Grammar::_default::_Digit_q(x0.clone())) as Rc<dyn ::std::ops::Fn(&_) -> _>))))
                        }
                        /// DafnyStandardLibraries-rs.dfy(10540,5)
                        pub fn NonEmptyDigits(cs: &FreshCursor) -> Rc<Result<Rc<Split<jnum>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut sp: Rc<Split<jdigits>> = crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::Digits(cs);
                            if sp.t()._Empty_q() {
                                Rc::new(Result::Failure::<Rc<Split<jdigits>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        error: Rc::new(CursorError::OtherError::<Rc<DeserializationError>> {
                                                    err: Rc::new(DeserializationError::EmptyNumber {})
                                                })
                                    })
                            } else {
                                Rc::new(Result::Success::<Rc<Split<jdigits>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: sp.clone()
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10550,5)
                        pub fn NonZeroInt(cs: &FreshCursor) -> Rc<Result<Rc<Split<jint>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::NonEmptyDigits(cs)
                        }
                        /// DafnyStandardLibraries-rs.dfy(10557,5)
                        pub fn OptionalMinus(cs: &FreshCursor) -> Rc<Split<jminus>> {
                            Cursor_::Split(AsRef::as_ref(&Cursor_::SkipIf(AsRef::as_ref(cs), &({
                                            Rc::new(move |c: &u8| -> bool{
            c.clone() == DafnyChar(char::from_u32(45).unwrap()).0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }))))
                        }
                        /// DafnyStandardLibraries-rs.dfy(10563,5)
                        pub fn OptionalSign(cs: &FreshCursor) -> Rc<Split<jsign>> {
                            Cursor_::Split(AsRef::as_ref(&Cursor_::SkipIf(AsRef::as_ref(cs), &({
                                            Rc::new(move |c: &u8| -> bool{
            c.clone() == DafnyChar(char::from_u32(45).unwrap()).0 as u8 || c.clone() == DafnyChar(char::from_u32(43).unwrap()).0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }))))
                        }
                        /// DafnyStandardLibraries-rs.dfy(10569,5)
                        pub fn TrimmedInt(cs: &FreshCursor) -> Rc<Result<Rc<Split<jint>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut sp: Rc<Split<View>> = Cursor_::Split(AsRef::as_ref(&Cursor_::SkipIf(AsRef::as_ref(cs), &({
                                                Rc::new(move |c: &u8| -> bool{
            c.clone() == DafnyChar(char::from_u32(48).unwrap()).0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                            }))));
                            if sp.t()._Empty_q() {
                                crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::NonZeroInt(sp.cs())
                            } else {
                                Rc::new(Result::Success::<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: sp.clone()
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10579,5)
                        pub fn Exp(cs: &FreshCursor) -> Rc<Result<Rc<Split<Rc<Maybe<Rc<jexp>>>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut __let_tmp_rhs0: Rc<Split<View>> = Cursor_::Split(AsRef::as_ref(&Cursor_::SkipIf(AsRef::as_ref(cs), &({
                                                Rc::new(move |c: &u8| -> bool{
            c.clone() == DafnyChar(char::from_u32(101).unwrap()).0 as u8 || c.clone() == DafnyChar(char::from_u32(69).unwrap()).0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                            }))));
                            let mut e: View = __let_tmp_rhs0.t().clone();
                            let mut cs: FreshCursor = __let_tmp_rhs0.cs().clone();
                            if e._Empty_q() {
                                Rc::new(Result::Success::<Rc<Split<Rc<Maybe<Rc<jexp>>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Rc::new(Split::SP::<Rc<Maybe<Rc<jexp>>>> {
                                                    t: Rc::new(Maybe::Empty::<Rc<jexp>> {}),
                                                    cs: cs.clone()
                                                })
                                    })
                            } else {
                                let mut __let_tmp_rhs1: Rc<Split<jsign>> = crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::OptionalSign(&cs);
                                let mut sign: jsign = __let_tmp_rhs1.t().clone();
                                let mut cs: FreshCursor = __let_tmp_rhs1.cs().clone();
                                let mut valueOrError0: Rc<Result<Rc<Split<jnum>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::NonEmptyDigits(&cs);
                                if valueOrError0.IsFailure() {
                                    valueOrError0.PropagateFailure::<Rc<Split<Rc<Maybe<Rc<jexp>>>>>>()
                                } else {
                                    let mut __let_tmp_rhs2: Rc<Split<jnum>> = valueOrError0.Extract();
                                    let mut num: jnum = __let_tmp_rhs2.t().clone();
                                    let mut cs: FreshCursor = __let_tmp_rhs2.cs().clone();
                                    Rc::new(Result::Success::<Rc<Split<Rc<Maybe<Rc<jexp>>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                            value: Rc::new(Split::SP::<Rc<Maybe<Rc<jexp>>>> {
                                                        t: Rc::new(Maybe::NonEmpty::<Rc<jexp>> {
                                                                    t: Rc::new(jexp::JExp {
                                                                                e: e.clone(),
                                                                                sign: sign.clone(),
                                                                                num: num.clone()
                                                                            })
                                                                }),
                                                        cs: cs.clone()
                                                    })
                                        })
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10589,5)
                        pub fn Frac(cs: &FreshCursor) -> Rc<Result<Rc<Split<Rc<Maybe<Rc<jfrac>>>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut __let_tmp_rhs0: Rc<Split<View>> = Cursor_::Split(AsRef::as_ref(&Cursor_::SkipIf(AsRef::as_ref(cs), &({
                                                Rc::new(move |c: &u8| -> bool{
            c.clone() == DafnyChar(char::from_u32(46).unwrap()).0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                            }))));
                            let mut period: View = __let_tmp_rhs0.t().clone();
                            let mut cs: FreshCursor = __let_tmp_rhs0.cs().clone();
                            if period._Empty_q() {
                                Rc::new(Result::Success::<Rc<Split<Rc<Maybe<Rc<jfrac>>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Rc::new(Split::SP::<Rc<Maybe<Rc<jfrac>>>> {
                                                    t: Rc::new(Maybe::Empty::<Rc<jfrac>> {}),
                                                    cs: cs.clone()
                                                })
                                    })
                            } else {
                                let mut valueOrError0: Rc<Result<Rc<Split<jnum>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::NonEmptyDigits(&cs);
                                if valueOrError0.IsFailure() {
                                    valueOrError0.PropagateFailure::<Rc<Split<Rc<Maybe<Rc<jfrac>>>>>>()
                                } else {
                                    let mut __let_tmp_rhs1: Rc<Split<jnum>> = valueOrError0.Extract();
                                    let mut num: jnum = __let_tmp_rhs1.t().clone();
                                    let mut cs: FreshCursor = __let_tmp_rhs1.cs().clone();
                                    Rc::new(Result::Success::<Rc<Split<Rc<Maybe<Rc<jfrac>>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                            value: Rc::new(Split::SP::<Rc<Maybe<Rc<jfrac>>>> {
                                                        t: Rc::new(Maybe::NonEmpty::<Rc<jfrac>> {
                                                                    t: Rc::new(jfrac::JFrac {
                                                                                period: period.clone(),
                                                                                num: num.clone()
                                                                            })
                                                                }),
                                                        cs: cs.clone()
                                                    })
                                        })
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10599,5)
                        pub fn NumberFromParts(minus: &Rc<Split<jminus>>, num: &Rc<Split<jint>>, frac: &Rc<Split<Rc<Maybe<Rc<jfrac>>>>>, exp: &Rc<Split<Rc<Maybe<Rc<jexp>>>>>) -> Rc<Split<Rc<jnumber>>> {
                            let mut sp: Rc<Split<Rc<jnumber>>> = Rc::new(Split::SP::<Rc<jnumber>> {
                                        t: Rc::new(jnumber::JNumber {
                                                    minus: minus.t().clone(),
                                                    num: num.t().clone(),
                                                    frac: frac.t().clone(),
                                                    exp: exp.t().clone()
                                                }),
                                        cs: exp.cs().clone()
                                    });
                            sp.clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(10622,5)
                        pub fn Number(cs: &FreshCursor) -> Rc<Result<Rc<Split<Rc<jnumber>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut minus: Rc<Split<jminus>> = crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::OptionalMinus(cs);
                            let mut valueOrError0: Rc<Result<Rc<Split<jint>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::TrimmedInt(minus.cs());
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<Rc<jnumber>>>>()
                            } else {
                                let mut num: Rc<Split<jint>> = valueOrError0.Extract();
                                let mut valueOrError1: Rc<Result<Rc<Split<Rc<Maybe<Rc<jfrac>>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::Frac(num.cs());
                                if valueOrError1.IsFailure() {
                                    valueOrError1.PropagateFailure::<Rc<Split<Rc<jnumber>>>>()
                                } else {
                                    let mut frac: Rc<Split<Rc<Maybe<Rc<jfrac>>>>> = valueOrError1.Extract();
                                    let mut valueOrError2: Rc<Result<Rc<Split<Rc<Maybe<Rc<jexp>>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::Exp(frac.cs());
                                    if valueOrError2.IsFailure() {
                                        valueOrError2.PropagateFailure::<Rc<Split<Rc<jnumber>>>>()
                                    } else {
                                        let mut exp: Rc<Split<Rc<Maybe<Rc<jexp>>>>> = valueOrError2.Extract();
                                        Rc::new(Result::Success::<Rc<Split<Rc<jnumber>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                value: crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::NumberFromParts(&minus, &num, &frac, &exp)
                                            })
                                    }
                                }
                            }
                        }
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(10687,3)
                pub mod ObjectParams {
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use ::std::rc::Rc;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Grammar::jcolon;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor_;
                    pub use ::std::convert::AsRef;
                    pub use ::dafny_runtime::DafnyChar;
                    pub use ::std::primitive::char;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use crate::Std::JSON::Grammar::jstring;
                    pub use crate::Std::JSON::Grammar::Structural;
                    pub use crate::Std::JSON::Grammar::Value;
                    pub use crate::Std::JSON::Grammar::jKeyValue;
                    pub use ::dafny_runtime::Sequence;
                    pub use crate::Std::JSON::ZeroCopy::Deserializer::Core::ValueParser;
                    pub use crate::Std::JSON::Utils::Parsers::Parser_;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(10691,5)
                        pub fn Colon(cs: &FreshCursor) -> Rc<Result<Rc<Split<jcolon>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> = Cursor_::AssertChar::<Rc<DeserializationError>>(AsRef::as_ref(cs), &DafnyChar(char::from_u32(58).unwrap()));
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<View>>>()
                            } else {
                                let mut cs: Cursor = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Cursor_::Split(AsRef::as_ref(&cs))
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10697,5)
                        pub fn KeyValueFromParts(k: &Rc<Split<Rc<jstring>>>, colon: &Rc<Split<Rc<Structural<jcolon>>>>, v: &Rc<Split<Rc<Value>>>) -> Rc<Split<Rc<jKeyValue>>> {
                            let mut sp: Rc<Split<Rc<jKeyValue>>> = Rc::new(Split::SP::<Rc<jKeyValue>> {
                                        t: Rc::new(jKeyValue::KeyValue {
                                                    k: k.t().clone(),
                                                    colon: colon.t().clone(),
                                                    v: v.t().clone()
                                                }),
                                        cs: v.cs().clone()
                                    });
                            sp.clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(10717,5)
                        pub fn ElementSpec(t: &Rc<jKeyValue>) -> Sequence<u8> {
                            crate::Std::JSON::ConcreteSyntax::Spec::_default::KeyValue(t)
                        }
                        /// DafnyStandardLibraries-rs.dfy(10722,5)
                        pub fn Element(cs: &FreshCursor, json: &ValueParser) -> Rc<Result<Rc<Split<Rc<jKeyValue>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Rc<Split<Rc<jstring>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Strings::_default::String(cs);
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<Rc<jKeyValue>>>>()
                            } else {
                                let mut k: Rc<Split<Rc<jstring>>> = valueOrError0.Extract();
                                let mut p: Rc<Parser_<jcolon, Rc<DeserializationError>>> = Rc::new(Parser_::Parser::<jcolon, Rc<DeserializationError>> {
                                            r#fn: Rc::new(move |x0: &FreshCursor| crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::Colon(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        });
                                let mut valueOrError1: Rc<Result<Rc<Split<Rc<Structural<jcolon>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::Structural::<jcolon>(k.cs(), &p);
                                if valueOrError1.IsFailure() {
                                    valueOrError1.PropagateFailure::<Rc<Split<Rc<jKeyValue>>>>()
                                } else {
                                    let mut colon: Rc<Split<Rc<Structural<jcolon>>>> = valueOrError1.Extract();
                                    let mut valueOrError2: Rc<Result<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>>> = json.r#fn()(colon.cs());
                                    if valueOrError2.IsFailure() {
                                        valueOrError2.PropagateFailure::<Rc<Split<Rc<jKeyValue>>>>()
                                    } else {
                                        let mut v: Rc<Split<Rc<Value>>> = valueOrError2.Extract();
                                        let mut kv: Rc<Split<Rc<jKeyValue>>> = crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::KeyValueFromParts(&k, &colon, &v);
                                        Rc::new(Result::Success::<Rc<Split<Rc<jKeyValue>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                value: kv.clone()
                                            })
                                    }
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10688,5)
                        pub fn OPEN() -> u8 {
                            DafnyChar(char::from_u32(123).unwrap()).0 as u8
                        }
                        /// DafnyStandardLibraries-rs.dfy(10689,5)
                        pub fn CLOSE() -> u8 {
                            DafnyChar(char::from_u32(125).unwrap()).0 as u8
                        }
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(10763,3)
                pub mod Objects {
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use crate::Std::JSON::ZeroCopy::Deserializer::Core::ValueParser;
                    pub use ::std::rc::Rc;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Grammar::Bracketed;
                    pub use crate::Std::JSON::Grammar::jlbrace;
                    pub use crate::Std::JSON::Grammar::jKeyValue;
                    pub use crate::Std::JSON::Grammar::jcomma;
                    pub use crate::Std::JSON::Grammar::jrbrace;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor_;
                    pub use ::std::convert::AsRef;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use crate::Std::JSON::Grammar::Structural;
                    pub use ::dafny_runtime::Sequence;
                    pub use crate::Std::JSON::Grammar::Suffixed;
                    pub use crate::Std::JSON::Grammar::Maybe;
                    pub use ::dafny_runtime::seq;
                    pub use crate::Std::JSON::ZeroCopy::Deserializer::Core::jopt;
                    pub use crate::Std::JSON::Utils::Views::Core::View_;
                    pub use ::dafny_runtime::truncate;
                    pub use ::dafny_runtime::int;
                    pub use crate::Std::JSON::Utils::Parsers::Parser_;
                    pub use ::dafny_runtime::DafnyChar;
                    pub use ::std::primitive::char;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(10781,5)
                        pub fn Object(cs: &FreshCursor, json: &ValueParser) -> Rc<Result<Rc<Split<Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::Bracketed(cs, json);
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>>()
                            } else {
                                let mut sp: Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>> = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: sp.clone()
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9944,5)
                        pub fn Open(cs: &FreshCursor) -> Rc<Result<Rc<Split<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> = Cursor_::AssertByte::<Rc<DeserializationError>>(AsRef::as_ref(cs), crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::OPEN());
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<View>>>()
                            } else {
                                let mut cs: Cursor = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Cursor_::Split(AsRef::as_ref(&cs))
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9950,5)
                        pub fn Close(cs: &FreshCursor) -> Rc<Result<Rc<Split<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> = Cursor_::AssertByte::<Rc<DeserializationError>>(AsRef::as_ref(cs), crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::CLOSE());
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<View>>>()
                            } else {
                                let mut cs: Cursor = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Cursor_::Split(AsRef::as_ref(&cs))
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9956,5)
                        pub fn BracketedFromParts(open: &Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen>>>>, elems: &Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>>, close: &Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>) -> Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>> {
                            let mut sp: Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>> = Rc::new(Split::SP::<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>> {
                                        t: Rc::new(Bracketed::Bracketed::<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose> {
                                                    l: open.t().clone(),
                                                    data: elems.t().clone(),
                                                    r: close.t().clone()
                                                }),
                                        cs: close.cs().clone()
                                    });
                            sp.clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(9989,5)
                        pub fn AppendWithSuffix(elems: &Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>>, elem: &Rc<Split<Rc<jKeyValue>>>, sep: &Rc<Split<Rc<Structural<jcomma>>>>) -> Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>> {
                            let mut suffixed: Rc<Suffixed<Rc<jKeyValue>, jcomma>> = Rc::new(Suffixed::Suffixed::<Rc<jKeyValue>, jcomma> {
                                        t: elem.t().clone(),
                                        suffix: Rc::new(Maybe::NonEmpty::<Rc<Structural<jcomma>>> {
                                                    t: sep.t().clone()
                                                })
                                    });
                            let mut _elems_k: Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>> = Rc::new(Split::SP::<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>> {
                                        t: elems.t().concat(&seq![suffixed.clone()]),
                                        cs: sep.cs().clone()
                                    });
                            _elems_k.clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(10039,5)
                        pub fn AppendLast(elems: &Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>>, elem: &Rc<Split<Rc<jKeyValue>>>, sep: &Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>) -> Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>> {
                            let mut suffixed: Rc<Suffixed<Rc<jKeyValue>, jcomma>> = Rc::new(Suffixed::Suffixed::<Rc<jKeyValue>, jcomma> {
                                        t: elem.t().clone(),
                                        suffix: Rc::new(Maybe::Empty::<Rc<Structural<jcomma>>> {})
                                    });
                            let mut _elems_k: Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>> = Rc::new(Split::SP::<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>> {
                                        t: elems.t().concat(&seq![suffixed.clone()]),
                                        cs: elem.cs().clone()
                                    });
                            _elems_k.clone()
                        }
                        /// DafnyStandardLibraries-rs.dfy(10085,5)
                        pub fn Elements(json: &ValueParser, open: &Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen>>>>, elems: &Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>>) -> Rc<Result<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut _r0 = json.clone();
                            let mut _r1 = open.clone();
                            let mut _r2 = elems.clone();
                            'TAIL_CALL_START: loop {
                                let json = _r0;
                                let open = _r1;
                                let elems = _r2;
                                let mut valueOrError0: Rc<Result<Rc<Split<Rc<jKeyValue>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::Element(elems.cs(), &json);
                                if valueOrError0.IsFailure() {
                                    return valueOrError0.PropagateFailure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>>();
                                } else {
                                    let mut elem: Rc<Split<Rc<jKeyValue>>> = valueOrError0.Extract();
                                    if elem.cs()._EOF_q() {
                                        return Rc::new(Result::Failure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                    error: Rc::new(CursorError::EOF::<Rc<DeserializationError>> {})
                                                });
                                    } else {
                                        let mut sep: Rc<Split<Rc<Structural<jopt>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::TryStructural(elem.cs());
                                        let mut s0: i16 = View_::Peek(AsRef::as_ref(sep.t().t()));
                                        if s0 == crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::SEPARATOR() as i16 && View_::Length(AsRef::as_ref(sep.t().t())) == truncate!(int!(1), u32) {
                                            let mut sep: Rc<Split<Rc<Structural<jcomma>>>> = sep.clone();
                                            let mut elems: Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::AppendWithSuffix(&elems, &elem, &sep);
                                            let mut _in0: ValueParser = json.clone();
                                            let mut _in1: Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen>>>> = open.clone();
                                            let mut _in2: Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>> = elems.clone();
                                            _r0 = _in0.clone();
                                            _r1 = _in1.clone();
                                            _r2 = _in2.clone();
                                            continue 'TAIL_CALL_START;
                                        } else {
                                            if s0 == crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::CLOSE() as i16 && View_::Length(AsRef::as_ref(sep.t().t())) == truncate!(int!(1), u32) {
                                                let mut sep: Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>> = sep.clone();
                                                let mut _elems_k: Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::AppendLast(&elems, &elem, &sep);
                                                let mut bracketed: Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::BracketedFromParts(&open, &_elems_k, &sep);
                                                return Rc::new(Result::Success::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                            value: bracketed.clone()
                                                        });
                                            } else {
                                                let mut separator: u8 = crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::SEPARATOR();
                                                let mut pr: Rc<Result<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = Rc::new(Result::Failure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                            error: Rc::new(CursorError::ExpectingAnyByte::<Rc<DeserializationError>> {
                                                                        expected_sq: seq![crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::CLOSE(), separator],
                                                                        b: s0
                                                                    })
                                                        });
                                                return pr.clone();
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10193,5)
                        pub fn Bracketed(cs: &FreshCursor, json: &ValueParser) -> Rc<Result<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::Structural::<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen>(cs, &Rc::new(Parser_::Parser::<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<DeserializationError>> {
                                            r#fn: Rc::new(move |x0: &FreshCursor| crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::Open(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        }));
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>>()
                            } else {
                                let mut open: Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen>>>> = valueOrError0.Extract();
                                let mut elems: Rc<Split<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>>> = Rc::new(Split::SP::<Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>> {
                                            t: seq![] as Sequence<Rc<Suffixed<Rc<jKeyValue>, jcomma>>>,
                                            cs: open.cs().clone()
                                        });
                                if Cursor_::Peek(AsRef::as_ref(open.cs())) == crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::CLOSE() as i16 {
                                    let mut p: Rc<Parser_<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose, Rc<DeserializationError>>> = Rc::new(Parser_::Parser::<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose, Rc<DeserializationError>> {
                                                r#fn: Rc::new(move |x0: &FreshCursor| crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::Close(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                            });
                                    let mut valueOrError1: Rc<Result<Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::Structural::<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>(open.cs(), &p);
                                    if valueOrError1.IsFailure() {
                                        valueOrError1.PropagateFailure::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>>()
                                    } else {
                                        let mut close: Rc<Split<Rc<Structural<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>> = valueOrError1.Extract();
                                        Rc::new(Result::Success::<Rc<Split<Rc<Bracketed<crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen, Rc<jKeyValue>, jcomma, crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose>>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                value: crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::BracketedFromParts(&open, &elems, &close)
                                            })
                                    }
                                } else {
                                    crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::Elements(json, &open, &elems)
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(9927,5)
                        pub fn SpecViewOpen() -> Rc<dyn ::std::ops::Fn(&crate::Std::JSON::ZeroCopy::Deserializer::Objects::jopen) -> Sequence<u8>> {
                            Rc::new(move |x0: &View| crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::SpecView()(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                        /// DafnyStandardLibraries-rs.dfy(9926,5)
                        pub fn SpecViewClose() -> Rc<dyn ::std::ops::Fn(&crate::Std::JSON::ZeroCopy::Deserializer::Objects::jclose) -> Sequence<u8>> {
                            Rc::new(move |x0: &View| crate::Std::JSON::ZeroCopy::Deserializer::Core::_default::SpecView()(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }
                        /// DafnyStandardLibraries-rs.dfy(9925,5)
                        pub fn SEPARATOR() -> u8 {
                            DafnyChar(char::from_u32(44).unwrap()).0 as u8
                        }
                    }

                    /// DafnyStandardLibraries-rs.dfy(10237,5)
                    pub type jopen = Rc<View_>;

                    /// An element of jopen
                    pub fn __init_jopen() -> Rc<View_> {
                        View_::OfBytes(&seq![crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::OPEN()])
                    }

                    /// DafnyStandardLibraries-rs.dfy(10241,5)
                    pub type jclose = Rc<View_>;

                    /// An element of jclose
                    pub fn __init_jclose() -> Rc<View_> {
                        View_::OfBytes(&seq![crate::Std::JSON::ZeroCopy::Deserializer::ObjectParams::_default::CLOSE()])
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(10480,3)
                pub mod Strings {
                    pub use crate::Std::JSON::Utils::Cursors::Cursor;
                    pub use ::std::rc::Rc;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use ::dafny_runtime::MaybePlacebo;
                    pub use ::dafny_runtime::integer_range;
                    pub use ::std::convert::Into;
                    pub use ::dafny_runtime::int;
                    pub use ::dafny_runtime::DafnyChar;
                    pub use ::std::primitive::char;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor_;
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Grammar::jquote;
                    pub use ::std::convert::AsRef;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use crate::Std::JSON::Grammar::jstring;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(10481,5)
                        pub fn StringBody(cs: &Cursor) -> Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut pr = MaybePlacebo::<Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>>>::new();
                            let mut escaped: bool = false;
                            let mut _hi0: u32 = cs.end().clone();
                            for _point_k in integer_range(cs.point().clone(), _hi0).map(Into::<u32>::into) {
                                let mut byte: u8 = cs.s().get(&int!((&_point_k).clone()));
                                if byte == DafnyChar(char::from_u32(34).unwrap()).0 as u8 && !escaped {
                                    pr = MaybePlacebo::from(Rc::new(Result::Success::<Rc<Cursor_>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                    value: Rc::new(Cursor_::Cursor {
                                                                s: cs.s().clone(),
                                                                beg: cs.beg().clone(),
                                                                point: _point_k,
                                                                end: cs.end().clone()
                                                            })
                                                }));
                                    return pr.read();
                                } else {
                                    if byte == DafnyChar(char::from_u32(92).unwrap()).0 as u8 {
                                        escaped = !escaped;
                                    } else {
                                        escaped = false;
                                    }
                                }
                            }
                            pr = MaybePlacebo::from(Rc::new(Result::Failure::<Cursor, Rc<CursorError<Rc<DeserializationError>>>> {
                                            error: Rc::new(CursorError::EOF::<Rc<DeserializationError>> {})
                                        }));
                            return pr.read();
                        }
                        /// DafnyStandardLibraries-rs.dfy(10503,5)
                        pub fn Quote(cs: &FreshCursor) -> Rc<Result<Rc<Split<jquote>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut valueOrError0: Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> = Cursor_::AssertChar::<Rc<DeserializationError>>(AsRef::as_ref(cs), &DafnyChar(char::from_u32(34).unwrap()));
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<View>>>()
                            } else {
                                let mut cs: Cursor = valueOrError0.Extract();
                                Rc::new(Result::Success::<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                        value: Cursor_::Split(AsRef::as_ref(&cs))
                                    })
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10509,5)
                        pub fn String(cs: &FreshCursor) -> Rc<Result<Rc<Split<Rc<jstring>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut origCs: FreshCursor = cs.clone();
                            let mut valueOrError0: Rc<Result<Rc<Split<jquote>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Strings::_default::Quote(cs);
                            if valueOrError0.IsFailure() {
                                valueOrError0.PropagateFailure::<Rc<Split<Rc<jstring>>>>()
                            } else {
                                let mut __let_tmp_rhs0: Rc<Split<jquote>> = valueOrError0.Extract();
                                let mut lq: jquote = __let_tmp_rhs0.t().clone();
                                let mut cs: FreshCursor = __let_tmp_rhs0.cs().clone();
                                let mut valueOrError1: Rc<Result<Cursor, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Strings::_default::StringBody(&cs);
                                if valueOrError1.IsFailure() {
                                    valueOrError1.PropagateFailure::<Rc<Split<Rc<jstring>>>>()
                                } else {
                                    let mut contents: Cursor = valueOrError1.Extract();
                                    let mut __let_tmp_rhs1: Rc<Split<View>> = Cursor_::Split(AsRef::as_ref(&contents));
                                    let mut contents: View = __let_tmp_rhs1.t().clone();
                                    let mut cs: FreshCursor = __let_tmp_rhs1.cs().clone();
                                    let mut valueOrError2: Rc<Result<Rc<Split<jquote>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Strings::_default::Quote(&cs);
                                    if valueOrError2.IsFailure() {
                                        valueOrError2.PropagateFailure::<Rc<Split<Rc<jstring>>>>()
                                    } else {
                                        let mut __let_tmp_rhs2: Rc<Split<jquote>> = valueOrError2.Extract();
                                        let mut rq: jquote = __let_tmp_rhs2.t().clone();
                                        let mut cs: FreshCursor = __let_tmp_rhs2.cs().clone();
                                        let mut result: Rc<Split<Rc<jstring>>> = Rc::new(Split::SP::<Rc<jstring>> {
                                                    t: Rc::new(jstring::JString {
                                                                lq: lq.clone(),
                                                                contents: contents.clone(),
                                                                rq: rq.clone()
                                                            }),
                                                    cs: cs.clone()
                                                });
                                        Rc::new(Result::Success::<Rc<Split<Rc<jstring>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                value: result.clone()
                                            })
                                    }
                                }
                            }
                        }
                    }
                }

                /// DafnyStandardLibraries-rs.dfy(10299,3)
                pub mod Values {
                    pub use crate::Std::JSON::Utils::Cursors::FreshCursor;
                    pub use ::std::rc::Rc;
                    pub use crate::Std::Wrappers::Result;
                    pub use crate::Std::JSON::Utils::Cursors::Split;
                    pub use crate::Std::JSON::Grammar::Value;
                    pub use crate::Std::JSON::Utils::Cursors::CursorError;
                    pub use crate::Std::JSON::Errors::DeserializationError;
                    pub use crate::Std::JSON::Utils::Cursors::Cursor_;
                    pub use ::std::convert::AsRef;
                    pub use ::dafny_runtime::DafnyChar;
                    pub use ::std::primitive::char;
                    pub use crate::Std::JSON::Grammar::Bracketed;
                    pub use crate::Std::JSON::Grammar::jlbrace;
                    pub use crate::Std::JSON::Grammar::jKeyValue;
                    pub use crate::Std::JSON::Grammar::jcomma;
                    pub use crate::Std::JSON::Grammar::jrbrace;
                    pub use crate::Std::JSON::Grammar::jlbracket;
                    pub use crate::Std::JSON::Grammar::jrbracket;
                    pub use crate::Std::JSON::Grammar::jstring;
                    pub use crate::Std::JSON::Utils::Views::Core::View;
                    pub use crate::Std::JSON::Grammar::jnumber;
                    pub use crate::Std::JSON::ZeroCopy::Deserializer::Core::ValueParser;
                    pub use crate::Std::JSON::Utils::Parsers::SubParser_;

                    pub struct _default {}

                    impl _default {
                        /// DafnyStandardLibraries-rs.dfy(10300,5)
                        pub fn Value(cs: &FreshCursor) -> Rc<Result<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>>> {
                            let mut c: i16 = Cursor_::Peek(AsRef::as_ref(cs));
                            if c == DafnyChar(char::from_u32(123).unwrap()).0 as i16 {
                                let mut valueOrError0: Rc<Result<Rc<Split<Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Objects::_default::Object(cs, &crate::Std::JSON::ZeroCopy::Deserializer::Values::_default::ValueParser(cs));
                                if valueOrError0.IsFailure() {
                                    valueOrError0.PropagateFailure::<Rc<Split<Rc<Value>>>>()
                                } else {
                                    let mut __let_tmp_rhs0: Rc<Split<Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>>> = valueOrError0.Extract();
                                    let mut obj: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = __let_tmp_rhs0.t().clone();
                                    let mut _cs_k: FreshCursor = __let_tmp_rhs0.cs().clone();
                                    let mut v: Rc<Value> = Rc::new(Value::Object {
                                                obj: obj.clone()
                                            });
                                    let mut sp: Rc<Split<Rc<Value>>> = Rc::new(Split::SP::<Rc<Value>> {
                                                t: v.clone(),
                                                cs: _cs_k.clone()
                                            });
                                    Rc::new(Result::Success::<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                            value: sp.clone()
                                        })
                                }
                            } else {
                                if c == DafnyChar(char::from_u32(91).unwrap()).0 as i16 {
                                    let mut valueOrError1: Rc<Result<Rc<Split<Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Arrays::_default::Array(cs, &crate::Std::JSON::ZeroCopy::Deserializer::Values::_default::ValueParser(cs));
                                    if valueOrError1.IsFailure() {
                                        valueOrError1.PropagateFailure::<Rc<Split<Rc<Value>>>>()
                                    } else {
                                        let mut __let_tmp_rhs1: Rc<Split<Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>>> = valueOrError1.Extract();
                                        let mut arr: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = __let_tmp_rhs1.t().clone();
                                        let mut _cs_k: FreshCursor = __let_tmp_rhs1.cs().clone();
                                        let mut v: Rc<Value> = Rc::new(Value::Array {
                                                    arr: arr.clone()
                                                });
                                        let mut sp: Rc<Split<Rc<Value>>> = Rc::new(Split::SP::<Rc<Value>> {
                                                    t: v.clone(),
                                                    cs: _cs_k.clone()
                                                });
                                        Rc::new(Result::Success::<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                value: sp.clone()
                                            })
                                    }
                                } else {
                                    if c == DafnyChar(char::from_u32(34).unwrap()).0 as i16 {
                                        let mut valueOrError2: Rc<Result<Rc<Split<Rc<jstring>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Strings::_default::String(cs);
                                        if valueOrError2.IsFailure() {
                                            valueOrError2.PropagateFailure::<Rc<Split<Rc<Value>>>>()
                                        } else {
                                            let mut __let_tmp_rhs2: Rc<Split<Rc<jstring>>> = valueOrError2.Extract();
                                            let mut str: Rc<jstring> = __let_tmp_rhs2.t().clone();
                                            let mut _cs_k: FreshCursor = __let_tmp_rhs2.cs().clone();
                                            Rc::new(Result::Success::<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                    value: Rc::new(Split::SP::<Rc<Value>> {
                                                                t: Rc::new(Value::String {
                                                                            str: str.clone()
                                                                        }),
                                                                cs: _cs_k.clone()
                                                            })
                                                })
                                        }
                                    } else {
                                        if c == DafnyChar(char::from_u32(116).unwrap()).0 as i16 {
                                            let mut valueOrError3: Rc<Result<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Constants::_default::Constant(cs, &crate::Std::JSON::Grammar::_default::TRUE());
                                            if valueOrError3.IsFailure() {
                                                valueOrError3.PropagateFailure::<Rc<Split<Rc<Value>>>>()
                                            } else {
                                                let mut __let_tmp_rhs3: Rc<Split<View>> = valueOrError3.Extract();
                                                let mut cst: View = __let_tmp_rhs3.t().clone();
                                                let mut _cs_k: FreshCursor = __let_tmp_rhs3.cs().clone();
                                                Rc::new(Result::Success::<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                        value: Rc::new(Split::SP::<Rc<Value>> {
                                                                    t: Rc::new(Value::Bool {
                                                                                b: cst.clone()
                                                                            }),
                                                                    cs: _cs_k.clone()
                                                                })
                                                    })
                                            }
                                        } else {
                                            if c == DafnyChar(char::from_u32(102).unwrap()).0 as i16 {
                                                let mut valueOrError4: Rc<Result<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Constants::_default::Constant(cs, &crate::Std::JSON::Grammar::_default::FALSE());
                                                if valueOrError4.IsFailure() {
                                                    valueOrError4.PropagateFailure::<Rc<Split<Rc<Value>>>>()
                                                } else {
                                                    let mut __let_tmp_rhs4: Rc<Split<View>> = valueOrError4.Extract();
                                                    let mut cst: View = __let_tmp_rhs4.t().clone();
                                                    let mut _cs_k: FreshCursor = __let_tmp_rhs4.cs().clone();
                                                    Rc::new(Result::Success::<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                            value: Rc::new(Split::SP::<Rc<Value>> {
                                                                        t: Rc::new(Value::Bool {
                                                                                    b: cst.clone()
                                                                                }),
                                                                        cs: _cs_k.clone()
                                                                    })
                                                        })
                                                }
                                            } else {
                                                if c == DafnyChar(char::from_u32(110).unwrap()).0 as i16 {
                                                    let mut valueOrError5: Rc<Result<Rc<Split<View>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Constants::_default::Constant(cs, &crate::Std::JSON::Grammar::_default::NULL());
                                                    if valueOrError5.IsFailure() {
                                                        valueOrError5.PropagateFailure::<Rc<Split<Rc<Value>>>>()
                                                    } else {
                                                        let mut __let_tmp_rhs5: Rc<Split<View>> = valueOrError5.Extract();
                                                        let mut cst: View = __let_tmp_rhs5.t().clone();
                                                        let mut _cs_k: FreshCursor = __let_tmp_rhs5.cs().clone();
                                                        Rc::new(Result::Success::<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                                value: Rc::new(Split::SP::<Rc<Value>> {
                                                                            t: Rc::new(Value::Null {
                                                                                        n: cst.clone()
                                                                                    }),
                                                                            cs: _cs_k.clone()
                                                                        })
                                                            })
                                                    }
                                                } else {
                                                    let mut valueOrError6: Rc<Result<Rc<Split<Rc<jnumber>>>, Rc<CursorError<Rc<DeserializationError>>>>> = crate::Std::JSON::ZeroCopy::Deserializer::Numbers::_default::Number(cs);
                                                    if valueOrError6.IsFailure() {
                                                        valueOrError6.PropagateFailure::<Rc<Split<Rc<Value>>>>()
                                                    } else {
                                                        let mut __let_tmp_rhs6: Rc<Split<Rc<jnumber>>> = valueOrError6.Extract();
                                                        let mut num: Rc<jnumber> = __let_tmp_rhs6.t().clone();
                                                        let mut _cs_k: FreshCursor = __let_tmp_rhs6.cs().clone();
                                                        let mut v: Rc<Value> = Rc::new(Value::Number {
                                                                    num: num.clone()
                                                                });
                                                        let mut sp: Rc<Split<Rc<Value>>> = Rc::new(Split::SP::<Rc<Value>> {
                                                                    t: v.clone(),
                                                                    cs: _cs_k.clone()
                                                                });
                                                        Rc::new(Result::Success::<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>> {
                                                                value: sp.clone()
                                                            })
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        /// DafnyStandardLibraries-rs.dfy(10428,5)
                        pub fn ValueParser(cs: &FreshCursor) -> ValueParser {
                            let mut pre: Rc<dyn ::std::ops::Fn(&FreshCursor) -> bool> = {
                                    let cs: FreshCursor = cs.clone();
                                    {
                                        let mut cs = cs.clone();
                                        Rc::new(move |_ps_k: &FreshCursor| -> bool{
            Cursor_::Length(AsRef::as_ref(_ps_k)) < Cursor_::Length(AsRef::as_ref(&cs))
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                    }
                                };
                            let mut r#fn: Rc<dyn ::std::ops::Fn(&FreshCursor) -> Rc<Result<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>>>> = {
                                    let pre: Rc<dyn ::std::ops::Fn(&FreshCursor) -> bool> = pre.clone();
                                    {
                                        Rc::new(move |_ps_k: &FreshCursor| -> Rc<Result<Rc<Split<Rc<Value>>>, Rc<CursorError<Rc<DeserializationError>>>>>{
            crate::Std::JSON::ZeroCopy::Deserializer::Values::_default::Value(_ps_k)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                    }
                                };
                            Rc::new(SubParser_::SubParser::<Rc<Value>, Rc<DeserializationError>> {
                                    r#fn: r#fn.clone()
                                })
                        }
                    }
                }
            }

            /// DafnyStandardLibraries-rs.dfy(10792,1)
            pub mod Serializer {
                pub use ::std::rc::Rc;
                pub use crate::Std::JSON::Grammar::Structural;
                pub use crate::Std::JSON::Grammar::Value;
                pub use crate::Std::Wrappers::Result;
                pub use ::dafny_runtime::Object;
                pub use crate::Std::JSON::Errors::SerializationError;
                pub use ::dafny_runtime::MaybePlacebo;
                pub use crate::Std::JSON::Utils::Views::Writers::Writer;
                pub use crate::Std::Wrappers::OutcomeResult;
                pub use crate::Std::JSON::Utils::Views::Writers::Writer_;
                pub use ::std::convert::AsRef;
                pub use ::dafny_runtime::int;
                pub use ::dafny_runtime::rd;
                pub use crate::Std::JSON::Grammar::Value::Null;
                pub use crate::Std::JSON::Grammar::jnull;
                pub use crate::Std::JSON::Grammar::Value::Bool;
                pub use crate::Std::JSON::Grammar::jbool;
                pub use crate::Std::JSON::Grammar::Value::String;
                pub use crate::Std::JSON::Grammar::jstring;
                pub use crate::Std::JSON::Grammar::Value::Number;
                pub use crate::Std::JSON::Grammar::jnumber;
                pub use crate::Std::JSON::Grammar::Bracketed;
                pub use crate::Std::JSON::Grammar::jlbrace;
                pub use crate::Std::JSON::Grammar::jKeyValue;
                pub use crate::Std::JSON::Grammar::jcomma;
                pub use crate::Std::JSON::Grammar::jrbrace;
                pub use crate::Std::JSON::Grammar::jlbracket;
                pub use crate::Std::JSON::Grammar::jrbracket;
                pub use crate::Std::JSON::Grammar::Maybe::NonEmpty;
                pub use crate::Std::JSON::Utils::Views::Core::View;
                pub use ::dafny_runtime::truncate;
                pub use crate::Std::JSON::Utils::Views::Writers::Chain;
                pub use crate::Std::JSON::Grammar::SuffixedSequence;
                pub use ::dafny_runtime::DafnyInt;
                pub use ::dafny_runtime::integer_range;
                pub use crate::Std::JSON::Grammar::Suffixed;
                pub use crate::Std::JSON::Grammar::Maybe::Empty;

                pub struct _default {}

                impl _default {
                    /// DafnyStandardLibraries-rs.dfy(10793,3)
                    pub fn Serialize(js: &Rc<Structural<Rc<Value>>>) -> Rc<Result<Object<[u8]>, Rc<SerializationError>>> {
                        let mut rbs = MaybePlacebo::<Rc<Result<Object<[u8]>, Rc<SerializationError>>>>::new();
                        let mut writer: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::Text(js);
                        let mut valueOrError0: Rc<OutcomeResult<Rc<SerializationError>>>;
                        valueOrError0 = crate::Std::Wrappers::_default::Need::<Rc<SerializationError>>(writer._Unsaturated_q(), &Rc::new(SerializationError::OutOfMemory {}));
                        if valueOrError0.IsFailure() {
                            rbs = MaybePlacebo::from(valueOrError0.PropagateFailure::<Object<[u8]>>());
                            return rbs.read();
                        };
                        let mut bs: Object<[u8]>;
                        let mut _out0: Object<[u8]>;
                        _out0 = Writer_::ToArray(AsRef::as_ref(&writer));
                        bs = _out0.clone();
                        rbs = MaybePlacebo::from(Rc::new(Result::Success::<Object<[u8]>, Rc<SerializationError>> {
                                        value: bs.clone()
                                    }));
                        return rbs.read();
                    }
                    /// DafnyStandardLibraries-rs.dfy(10803,3)
                    pub fn SerializeTo(js: &Rc<Structural<Rc<Value>>>, dest: &Object<[u8]>) -> Rc<Result<u32, Rc<SerializationError>>> {
                        let mut len = MaybePlacebo::<Rc<Result<u32, Rc<SerializationError>>>>::new();
                        let mut writer: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::Text(js);
                        let mut valueOrError0: Rc<OutcomeResult<Rc<SerializationError>>>;
                        valueOrError0 = crate::Std::Wrappers::_default::Need::<Rc<SerializationError>>(writer._Unsaturated_q(), &Rc::new(SerializationError::OutOfMemory {}));
                        if valueOrError0.IsFailure() {
                            len = MaybePlacebo::from(valueOrError0.PropagateFailure::<u32>());
                            return len.read();
                        };
                        let mut valueOrError1: Rc<OutcomeResult<Rc<SerializationError>>>;
                        valueOrError1 = crate::Std::Wrappers::_default::Need::<Rc<SerializationError>>(!(int!(rd!(dest.clone()).len()) < int!(writer.length().clone())), &Rc::new(SerializationError::OutOfMemory {}));
                        if valueOrError1.IsFailure() {
                            len = MaybePlacebo::from(valueOrError1.PropagateFailure::<u32>());
                            return len.read();
                        };
                        Writer_::CopyTo(AsRef::as_ref(&writer), dest);
                        len = MaybePlacebo::from(Rc::new(Result::Success::<u32, Rc<SerializationError>> {
                                        value: writer.length().clone()
                                    }));
                        return len.read();
                    }
                    /// DafnyStandardLibraries-rs.dfy(10817,3)
                    pub fn Text(js: &Rc<Structural<Rc<Value>>>) -> Writer {
                        crate::Std::JSON::ZeroCopy::Serializer::_default::JSON(js, &Writer_::Empty())
                    }
                    /// DafnyStandardLibraries-rs.dfy(10823,3)
                    pub fn JSON(js: &Rc<Structural<Rc<Value>>>, writer: &Writer) -> Writer {
                        Writer_::Append(AsRef::as_ref(&Writer_::Then(AsRef::as_ref(&Writer_::Append(AsRef::as_ref(writer), js.before())), {
                                        let js: Rc<Structural<Rc<Value>>> = js.clone();
                                        &({
                                            let mut js = js.clone();
                                            Rc::new(move |wr: &Writer| -> Writer{
            crate::Std::JSON::ZeroCopy::Serializer::_default::Value(js.t(), wr)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        })
                                    })), js.after())
                    }
                    /// DafnyStandardLibraries-rs.dfy(10830,3)
                    pub fn Value(v: &Rc<Value>, writer: &Writer) -> Writer {
                        let mut _source0: Rc<Value> = v.clone();
                        if matches!((&_source0).as_ref(), Null{ .. }) {
                            let mut ___mcc_h0: jnull = _source0.n().clone();
                            let mut n: jnull = ___mcc_h0.clone();
                            let mut wr: Writer = Writer_::Append(AsRef::as_ref(writer), &n);
                            wr.clone()
                        } else {
                            if matches!((&_source0).as_ref(), Bool{ .. }) {
                                let mut ___mcc_h1: jbool = _source0.b().clone();
                                let mut b: jbool = ___mcc_h1.clone();
                                let mut wr: Writer = Writer_::Append(AsRef::as_ref(writer), &b);
                                wr.clone()
                            } else {
                                if matches!((&_source0).as_ref(), String{ .. }) {
                                    let mut ___mcc_h2: Rc<jstring> = _source0.str().clone();
                                    let mut str: Rc<jstring> = ___mcc_h2.clone();
                                    let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::String(&str, writer);
                                    wr.clone()
                                } else {
                                    if matches!((&_source0).as_ref(), Number{ .. }) {
                                        let mut ___mcc_h3: Rc<jnumber> = _source0.num().clone();
                                        let mut num: Rc<jnumber> = ___mcc_h3.clone();
                                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::Number(&num, writer);
                                        wr.clone()
                                    } else {
                                        if matches!((&_source0).as_ref(), crate::Std::JSON::Grammar::Value::Object{ .. }) {
                                            let mut ___mcc_h4: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = _source0.obj().clone();
                                            let mut obj: Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>> = ___mcc_h4.clone();
                                            let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::Object(&obj, writer);
                                            wr.clone()
                                        } else {
                                            let mut ___mcc_h5: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = _source0.arr().clone();
                                            let mut arr: Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>> = ___mcc_h5.clone();
                                            let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::Array(&arr, writer);
                                            wr.clone()
                                        }
                                    }
                                }
                            }
                        }
                    }
                    /// DafnyStandardLibraries-rs.dfy(10900,3)
                    pub fn String(str: &Rc<jstring>, writer: &Writer) -> Writer {
                        Writer_::Append(AsRef::as_ref(&Writer_::Append(AsRef::as_ref(&Writer_::Append(AsRef::as_ref(writer), str.lq())), str.contents())), str.rq())
                    }
                    /// DafnyStandardLibraries-rs.dfy(11018,3)
                    pub fn Number(num: &Rc<jnumber>, writer: &Writer) -> Writer {
                        let mut wr1: Writer = Writer_::Append(AsRef::as_ref(&Writer_::Append(AsRef::as_ref(writer), num.minus())), num.num());
                        let mut wr2: Rc<Writer_> = if matches!(num.frac().as_ref(), NonEmpty{ .. }) {
                                Writer_::Append(AsRef::as_ref(&Writer_::Append(AsRef::as_ref(&wr1), num.frac().t().period())), num.frac().t().num())
                            } else {
                                wr1.clone()
                            };
                        let mut wr3: Rc<Writer_> = if matches!(num.exp().as_ref(), NonEmpty{ .. }) {
                                Writer_::Append(AsRef::as_ref(&Writer_::Append(AsRef::as_ref(&wr2.Append(num.exp().t().e())), num.exp().t().sign())), num.exp().t().num())
                            } else {
                                wr2.clone()
                            };
                        let mut wr: Rc<Writer_> = wr3.clone();
                        wr.clone()
                    }
                    /// DafnyStandardLibraries-rs.dfy(11057,3)
                    pub fn StructuralView(st: &Rc<Structural<View>>, writer: &Writer) -> Writer {
                        Writer_::Append(AsRef::as_ref(&Writer_::Append(AsRef::as_ref(&Writer_::Append(AsRef::as_ref(writer), st.before())), st.t())), st.after())
                    }
                    /// DafnyStandardLibraries-rs.dfy(11085,3)
                    pub fn Object(obj: &Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>, writer: &Writer) -> Writer {
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::StructuralView(obj.l(), writer);
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::Members(obj, &wr);
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::StructuralView(obj.r(), &wr);
                        wr.clone()
                    }
                    /// DafnyStandardLibraries-rs.dfy(11118,3)
                    pub fn Array(arr: &Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>, writer: &Writer) -> Writer {
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::StructuralView(arr.l(), writer);
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::Items(arr, &wr);
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::StructuralView(arr.r(), &wr);
                        wr.clone()
                    }
                    /// DafnyStandardLibraries-rs.dfy(11134,3)
                    pub fn Members(obj: &Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>, writer: &Writer) -> Writer {
                        let mut wr: Writer = Rc::new(Writer_::Writer {
                                    length: truncate!(int!(0), u32),
                                    chain: Rc::new(Chain::Empty {})
                                });
                        let mut _out0: Writer;
                        _out0 = crate::Std::JSON::ZeroCopy::Serializer::_default::MembersImpl(obj, writer);
                        wr = _out0.clone();
                        return wr.clone();
                    }
                    /// DafnyStandardLibraries-rs.dfy(11144,3)
                    pub fn Items(arr: &Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>, writer: &Writer) -> Writer {
                        let mut wr: Writer = Rc::new(Writer_::Writer {
                                    length: truncate!(int!(0), u32),
                                    chain: Rc::new(Chain::Empty {})
                                });
                        let mut _out0: Writer;
                        _out0 = crate::Std::JSON::ZeroCopy::Serializer::_default::ItemsImpl(arr, writer);
                        wr = _out0.clone();
                        return wr.clone();
                    }
                    /// DafnyStandardLibraries-rs.dfy(11248,3)
                    pub fn MembersImpl(obj: &Rc<Bracketed<jlbrace, Rc<jKeyValue>, jcomma, jrbrace>>, writer: &Writer) -> Writer {
                        let mut wr: Writer = Rc::new(Writer_::Writer {
                                    length: truncate!(int!(0), u32),
                                    chain: Rc::new(Chain::Empty {})
                                });
                        wr = writer.clone();
                        let mut members: SuffixedSequence<Rc<jKeyValue>, jcomma> = obj.data().clone();
                        let mut _hi0: DafnyInt = members.cardinality();
                        for i in integer_range(int!(0), _hi0.clone()) {
                            wr = crate::Std::JSON::ZeroCopy::Serializer::_default::Member(&members.get(&i), &wr);
                        }
                        return wr.clone();
                    }
                    /// DafnyStandardLibraries-rs.dfy(11267,3)
                    pub fn ItemsImpl(arr: &Rc<Bracketed<jlbracket, Rc<Value>, jcomma, jrbracket>>, writer: &Writer) -> Writer {
                        let mut wr: Writer = Rc::new(Writer_::Writer {
                                    length: truncate!(int!(0), u32),
                                    chain: Rc::new(Chain::Empty {})
                                });
                        wr = writer.clone();
                        let mut items: SuffixedSequence<Rc<Value>, jcomma> = arr.data().clone();
                        let mut _hi0: DafnyInt = items.cardinality();
                        for i in integer_range(int!(0), _hi0.clone()) {
                            wr = crate::Std::JSON::ZeroCopy::Serializer::_default::Item(&items.get(&i), &wr);
                        }
                        return wr.clone();
                    }
                    /// DafnyStandardLibraries-rs.dfy(11291,3)
                    pub fn Member(m: &Rc<Suffixed<Rc<jKeyValue>, jcomma>>, writer: &Writer) -> Writer {
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::String(m.t().k(), writer);
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::StructuralView(m.t().colon(), &wr);
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::Value(m.t().v(), &wr);
                        let mut wr: Rc<Writer_> = if matches!(m.suffix().as_ref(), Empty{ .. }) {
                                wr.clone()
                            } else {
                                crate::Std::JSON::ZeroCopy::Serializer::_default::StructuralView(m.suffix().t(), &wr)
                            };
                        wr.clone()
                    }
                    /// DafnyStandardLibraries-rs.dfy(11317,3)
                    pub fn Item(m: &Rc<Suffixed<Rc<Value>, jcomma>>, writer: &Writer) -> Writer {
                        let mut wr: Writer = crate::Std::JSON::ZeroCopy::Serializer::_default::Value(m.t(), writer);
                        let mut wr: Rc<Writer_> = if matches!(m.suffix().as_ref(), Empty{ .. }) {
                                wr.clone()
                            } else {
                                crate::Std::JSON::ZeroCopy::Serializer::_default::StructuralView(m.suffix().t(), &wr)
                            };
                        wr.clone()
                    }
                }
            }
        }
    }

    /// DafnyStandardLibraries-rs.dfy(11349,1)
    pub mod Math {
        pub use ::dafny_runtime::DafnyInt;
        pub use ::dafny_runtime::int;

        pub struct _default {}

        impl _default {
            /// DafnyStandardLibraries-rs.dfy(11350,3)
            pub fn Min(a: &DafnyInt, b: &DafnyInt) -> DafnyInt {
                if a.clone() < b.clone() {
                    a.clone()
                } else {
                    b.clone()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(11358,3)
            pub fn Min3(a: &DafnyInt, b: &DafnyInt, c: &DafnyInt) -> DafnyInt {
                crate::Std::Math::_default::Min(a, &crate::Std::Math::_default::Min(b, c))
            }
            /// DafnyStandardLibraries-rs.dfy(11363,3)
            pub fn Max(a: &DafnyInt, b: &DafnyInt) -> DafnyInt {
                if a.clone() < b.clone() {
                    b.clone()
                } else {
                    a.clone()
                }
            }
            /// DafnyStandardLibraries-rs.dfy(11371,3)
            pub fn Max3(a: &DafnyInt, b: &DafnyInt, c: &DafnyInt) -> DafnyInt {
                crate::Std::Math::_default::Max(a, &crate::Std::Math::_default::Max(b, c))
            }
            /// DafnyStandardLibraries-rs.dfy(11376,3)
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
        /// DafnyStandardLibraries-rs.dfy(12511,1)
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
                /// DafnyStandardLibraries-rs.dfy(12512,3)
                pub fn ToInput(r: &Sequence<DafnyChar>) -> crate::Std::Parsers::InputString::Input {
                    Rc::new(Slice::Slice::<DafnyChar> {
                            data: r.clone(),
                            start: int!(0),
                            end: r.cardinality()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12518,3)
                pub fn View(_self: &crate::Std::Parsers::InputString::Input) -> Sequence<DafnyChar> {
                    Slice::<DafnyChar>::View(AsRef::as_ref(_self))
                }
                /// DafnyStandardLibraries-rs.dfy(12524,3)
                pub fn Length(_self: &crate::Std::Parsers::InputString::Input) -> nat {
                    Slice::<DafnyChar>::Length(AsRef::as_ref(_self))
                }
                /// DafnyStandardLibraries-rs.dfy(12529,3)
                pub fn CharAt(_self: &crate::Std::Parsers::InputString::Input, i: &DafnyInt) -> DafnyChar {
                    Slice::<DafnyChar>::At(AsRef::as_ref(_self), i)
                }
                /// DafnyStandardLibraries-rs.dfy(12535,3)
                pub fn Drop(_self: &crate::Std::Parsers::InputString::Input, start: &DafnyInt) -> crate::Std::Parsers::InputString::Input {
                    Slice::<DafnyChar>::Drop(AsRef::as_ref(_self), start)
                }
                /// DafnyStandardLibraries-rs.dfy(12541,3)
                pub fn Slice(_self: &crate::Std::Parsers::InputString::Input, start: &DafnyInt, end: &DafnyInt) -> crate::Std::Parsers::InputString::Input {
                    Slice::<DafnyChar>::Sub(AsRef::as_ref(_self), start, end)
                }
                /// DafnyStandardLibraries-rs.dfy(12552,3)
                pub fn Equals(_self: &crate::Std::Parsers::InputString::Input, other: &crate::Std::Parsers::InputString::Input) -> bool {
                    _self.clone() == other.clone()
                }
            }

            /// DafnyStandardLibraries-rs.dfy(12560,3)
            pub type Input = Rc<Slice<DafnyChar>>;
        }

        /// DafnyStandardLibraries-rs.dfy(12442,1)
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
                /// DafnyStandardLibraries-rs.dfy(12443,3)
                pub fn ToInput(other: &Sequence<DafnyChar>) -> Input {
                    Rc::new(Slice::Slice::<DafnyChar> {
                            data: other.clone(),
                            start: int!(0),
                            end: other.cardinality()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12449,3)
                pub fn ToInputEnd(other: &Sequence<DafnyChar>, fromEnd: &DafnyInt) -> Input {
                    Rc::new(Slice::Slice::<DafnyChar> {
                            data: other.clone(),
                            start: other.cardinality() - fromEnd.clone(),
                            end: other.cardinality()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12456,3)
                pub fn S(s: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<DafnyChar>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<DafnyChar>> {
                            apply: crate::Std::Parsers::StringParsers::_default::String(s)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12461,3)
                pub fn String(s: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<DafnyChar>>> {
                    crate::Std::Parsers::StringBuilders::_default::S(s)
                }
                /// DafnyStandardLibraries-rs.dfy(12473,3)
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
                /// DafnyStandardLibraries-rs.dfy(12478,3)
                pub fn DebugSummaryInput(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                    crate::Std::Parsers::StringParsers::_default::DebugSummaryInput(name, input)
                }
                /// DafnyStandardLibraries-rs.dfy(12483,3)
                pub fn PrintDebugSummaryOutput<_R: DafnyType>(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>, result: &Rc<ParseResult<_R>>) -> () {
                    crate::Std::Parsers::StringParsers::_default::PrintDebugSummaryOutput::<_R>(name, input, result);
                    return ();
                }
                /// DafnyStandardLibraries-rs.dfy(12488,3)
                pub fn FailureToString<_R: DafnyType>(input: &Sequence<DafnyChar>, result: &Rc<ParseResult<_R>>) -> Sequence<DafnyChar> {
                    crate::Std::Parsers::StringParsers::_default::FailureToString::<_R>(input, result, &int!(-1))
                }
                /// DafnyStandardLibraries-rs.dfy(12494,3)
                pub fn Apply<_T: DafnyType>(parser: &Rc<crate::Std::Parsers::StringBuilders::B<_T>>, input: &Sequence<DafnyChar>) -> Rc<ParseResult<_T>> {
                    crate::Std::Parsers::StringParsers::_default::Apply::<_T>(parser.apply(), input)
                }
                /// DafnyStandardLibraries-rs.dfy(12499,3)
                pub fn InputToString(input: &Input) -> Sequence<DafnyChar> {
                    crate::Std::Parsers::InputString::_default::View(input)
                }
                /// DafnyStandardLibraries-rs.dfy(11388,3)
                pub fn SucceedWith<_T: DafnyType>(t: &_T) -> Rc<crate::Std::Parsers::StringBuilders::B<_T>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_T> {
                            apply: crate::Std::Parsers::StringParsers::_default::SucceedWith::<_T>(t)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11393,3)
                pub fn FailWith<_T: DafnyType>(message: &Sequence<DafnyChar>, level: &Rc<FailureLevel>) -> Rc<crate::Std::Parsers::StringBuilders::B<_T>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_T> {
                            apply: crate::Std::Parsers::StringParsers::_default::FailWith::<_T>(message, level)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11398,3)
                pub fn ResultWith<_R: DafnyType>(result: &Rc<ParseResult<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_R> {
                            apply: crate::Std::Parsers::StringParsers::_default::ResultWith::<_R>(result)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11405,3)
                pub fn MId<_R: DafnyType>(r: &_R) -> _R {
                    r.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(11410,3)
                pub fn MapIdentity<_R: DafnyType>(r: &_R) -> _R {
                    r.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(11415,3)
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
                /// DafnyStandardLibraries-rs.dfy(11425,3)
                pub fn Or<_R: DafnyType>(alternatives: &Sequence<Rc<crate::Std::Parsers::StringBuilders::B<_R>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    crate::Std::Parsers::StringBuilders::_default::O::<_R>(alternatives)
                }
                /// DafnyStandardLibraries-rs.dfy(11433,3)
                pub fn CharTest(test: &Rc<dyn ::std::ops::Fn(&DafnyChar) -> bool>, name: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<DafnyChar>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<DafnyChar> {
                            apply: crate::Std::Parsers::StringParsers::_default::CharTest(test, name)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11438,3)
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
                /// DafnyStandardLibraries-rs.dfy(11443,3)
                pub fn Recursive<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Parsers::StringBuilders::B<_R>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    crate::Std::Parsers::StringBuilders::_default::Rec::<_R>(underlying)
                }
                /// DafnyStandardLibraries-rs.dfy(11448,3)
                pub fn InputLength(input: &Input) -> nat {
                    crate::Std::Parsers::InputString::_default::Length(input)
                }
                /// DafnyStandardLibraries-rs.dfy(11453,3)
                pub fn NonProgressing(input1: &Input, input2: &Input) -> bool {
                    !(crate::Std::Parsers::StringBuilders::_default::InputLength(input2) < crate::Std::Parsers::StringBuilders::_default::InputLength(input1))
                }
                /// DafnyStandardLibraries-rs.dfy(11458,3)
                pub fn RecursiveProgressError<_R: DafnyType>(name: &Sequence<DafnyChar>, input1: &Input, input2: &Input) -> Rc<ParseResult<_R>> {
                    crate::Std::Parsers::StringParsers::_default::RecursiveProgressError::<_R>(name, input1, input2)
                }
                /// DafnyStandardLibraries-rs.dfy(11464,3)
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
                /// DafnyStandardLibraries-rs.dfy(11469,3)
                pub fn RecursiveNoStack<_R: DafnyType>(underlying: &Rc<crate::Std::Parsers::StringBuilders::B<Rc<crate::Std::Parsers::StringBuilders::RecNoStackResult<_R>>>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    crate::Std::Parsers::StringBuilders::_default::RecNoStack::<_R>(underlying)
                }
                /// DafnyStandardLibraries-rs.dfy(11474,3)
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
                    let __pat_let6_0: (_R, Input) = p.Extract();
                    {
                        let r: _R = __pat_let6_0.0.clone();
                        {
                            let remaining2: Input = __pat_let6_0.1.clone();
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
                    let __pat_let7_0: (_R, Input) = p.Extract();
                    {
                        let r: _R = __pat_let7_0.0.clone();
                        {
                            let remaining2: Input = __pat_let7_0.1.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11489,3)
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
                /// DafnyStandardLibraries-rs.dfy(11494,3)
                pub fn RecursiveMap<_R: DafnyType>(underlying: &Map<Sequence<DafnyChar>, Rc<crate::Std::Parsers::StringBuilders::RecMapDef<_R>>>, startFun: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringBuilders::B<_R>> {
                    crate::Std::Parsers::StringBuilders::_default::RecMap::<_R>(underlying, startFun)
                }
                /// DafnyStandardLibraries-rs.dfy(12466,3)
                pub fn Int() -> Rc<crate::Std::Parsers::StringBuilders::B<DafnyInt>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<DafnyInt> {
                            apply: crate::Std::Parsers::StringParsers::_default::Int()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12467,3)
                pub fn Nat() -> Rc<crate::Std::Parsers::StringBuilders::B<nat>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<nat> {
                            apply: crate::Std::Parsers::StringParsers::_default::Nat()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12468,3)
                pub fn Digit() -> Rc<crate::Std::Parsers::StringBuilders::B<DafnyChar>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<DafnyChar> {
                            apply: crate::Std::Parsers::StringParsers::_default::Digit()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12469,3)
                pub fn DigitNumber() -> Rc<crate::Std::Parsers::StringBuilders::B<nat>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<nat> {
                            apply: crate::Std::Parsers::StringParsers::_default::DigitNumber()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12470,3)
                pub fn WS() -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<DafnyChar>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<DafnyChar>> {
                            apply: crate::Std::Parsers::StringParsers::_default::WS()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12471,3)
                pub fn Whitespace() -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<DafnyChar>>> {
                    crate::Std::Parsers::StringBuilders::_default::WS()
                }
                /// DafnyStandardLibraries-rs.dfy(11403,3)
                pub fn Nothing() -> Rc<crate::Std::Parsers::StringBuilders::B<()>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<()> {
                            apply: crate::Std::Parsers::StringParsers::_default::Epsilon()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11430,3)
                pub fn EOS() -> Rc<crate::Std::Parsers::StringBuilders::B<()>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<()> {
                            apply: crate::Std::Parsers::StringParsers::_default::EndOfString()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11431,3)
                pub fn EndOfString() -> Rc<crate::Std::Parsers::StringBuilders::B<()>> {
                    crate::Std::Parsers::StringBuilders::_default::EOS()
                }
            }

            /// DafnyStandardLibraries-rs.dfy(11516,3)
            #[derive(Clone)]
            pub enum B<R: DafnyType> {
                B {
                    apply: Rc<dyn ::std::ops::Fn(&Input) -> Rc<ParseResult<R>>>
                }
            }

            impl<R: DafnyType> B<R> {
                /// DafnyStandardLibraries-rs.dfy(11517,5)
                pub fn Apply(&self, input: &Sequence<DafnyChar>) -> Rc<ParseResult<R>> {
                    self.apply()(&crate::Std::Parsers::StringBuilders::_default::ToInput(input))
                }
                /// DafnyStandardLibraries-rs.dfy(11522,5)
                pub fn _q(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<Option<R>>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Rc<Option<R>>> {
                            apply: crate::Std::Parsers::StringParsers::_default::Maybe::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11527,5)
                pub fn Option(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Rc<Option<R>>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Rc<Option<R>>> {
                            apply: crate::Std::Parsers::StringParsers::_default::Maybe::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11532,5)
                pub fn __q_q(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::_q::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11537,5)
                pub fn FailureResetsInput(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::_q::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11542,5)
                pub fn e_I<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_U> {
                            apply: crate::Std::Parsers::StringParsers::_default::ConcatKeepRight::<R, _U>(self.apply(), other.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11547,5)
                pub fn ConcatKeepRight<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    self.e_I::<_U>(other)
                }
                /// DafnyStandardLibraries-rs.dfy(11552,5)
                pub fn I_e<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::ConcatKeepLeft::<R, _U>(self.apply(), other.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11557,5)
                pub fn ConcatKeepLeft<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    self.I_e::<_U>(other)
                }
                /// DafnyStandardLibraries-rs.dfy(11562,5)
                pub fn I_I<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<(R, _U)>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<(R, _U)> {
                            apply: crate::Std::Parsers::StringParsers::_default::Concat::<R, _U>(self.apply(), other.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11567,5)
                pub fn Concat<_U: DafnyType>(&self, other: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<(R, _U)>> {
                    self.I_I::<_U>(other)
                }
                /// DafnyStandardLibraries-rs.dfy(11572,5)
                pub fn If<_U: DafnyType>(&self, cond: &Rc<crate::Std::Parsers::StringBuilders::B<_U>>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::If::<_U, R>(cond.apply(), self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11577,5)
                pub fn M<_U: DafnyType>(&self, mappingFunc: &Rc<dyn ::std::ops::Fn(&R) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_U> {
                            apply: crate::Std::Parsers::StringParsers::_default::Map::<R, _U>(self.apply(), mappingFunc)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11582,5)
                pub fn Map<_U: DafnyType>(&self, mappingFunc: &Rc<dyn ::std::ops::Fn(&R) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    self.M::<_U>(mappingFunc)
                }
                /// DafnyStandardLibraries-rs.dfy(11587,5)
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
                let __pat_let8_0: (_R1, _R2) = (&unfolder)(x);
                {
                    let x: (_R1, _R2) = __pat_let8_0.clone();
                    (&mappingFunc)(&x.0.clone(), &x.1.clone())
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        })
                                    })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11592,5)
                pub fn Map2<_R1: DafnyType, _R2: DafnyType, _U: DafnyType>(&self, unfolder: &Rc<dyn ::std::ops::Fn(&R) -> (_R1, _R2)>, mappingFunc: &Rc<dyn ::std::ops::Fn(&_R1, &_R2) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    self.M2::<_R1, _R2, _U>(unfolder, mappingFunc)
                }
                /// DafnyStandardLibraries-rs.dfy(11597,5)
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
                let __pat_let9_0: (_R1, _R2, _R3) = (&unfolder)(x);
                {
                    let x: (_R1, _R2, _R3) = __pat_let9_0.clone();
                    (&mappingFunc)(&x.0.clone(), &x.1.clone(), &x.2.clone())
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                        })
                                    })
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11602,5)
                pub fn Map3<_R1: DafnyType, _R2: DafnyType, _R3: DafnyType, _U: DafnyType>(&self, unfolder: &Rc<dyn ::std::ops::Fn(&R) -> (_R1, _R2, _R3)>, mappingFunc: &Rc<dyn ::std::ops::Fn(&_R1, &_R2, &_R3) -> _U>) -> Rc<crate::Std::Parsers::StringBuilders::B<_U>> {
                    self.M3::<_R1, _R2, _R3, _U>(unfolder, mappingFunc)
                }
                /// DafnyStandardLibraries-rs.dfy(11607,5)
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
                /// DafnyStandardLibraries-rs.dfy(11612,5)
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
                /// DafnyStandardLibraries-rs.dfy(11617,5)
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
                /// DafnyStandardLibraries-rs.dfy(11622,5)
                pub fn Debug<_D: DafnyType>(&self, name: &Sequence<DafnyChar>, onEnter: &Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>, &Input) -> _D>, onExit: &Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>, &_D, &Rc<ParseResult<R>>) -> ()>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::Debug::<R, _D>(self.apply(), name, onEnter, onExit)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11627,5)
                pub fn RepFold<_A: DafnyType>(&self, init: &_A, combine: &Rc<dyn ::std::ops::Fn(&_A, &R) -> _A>) -> Rc<crate::Std::Parsers::StringBuilders::B<_A>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<_A> {
                            apply: crate::Std::Parsers::StringParsers::_default::Rep::<_A, R>(self.apply(), combine, init)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11632,5)
                pub fn RepeatFold<_A: DafnyType>(&self, init: &_A, combine: &Rc<dyn ::std::ops::Fn(&_A, &R) -> _A>) -> Rc<crate::Std::Parsers::StringBuilders::B<_A>> {
                    self.RepFold::<_A>(init, combine)
                }
                /// DafnyStandardLibraries-rs.dfy(11637,5)
                pub fn RepSep<_K: DafnyType>(&self, separator: &Rc<crate::Std::Parsers::StringBuilders::B<_K>>) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<R>> {
                            apply: crate::Std::Parsers::StringParsers::_default::RepSep::<R, _K>(self.apply(), separator.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11642,5)
                pub fn RepeatSeparator<_K: DafnyType>(&self, separator: &Rc<crate::Std::Parsers::StringBuilders::B<_K>>) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    self.RepSep::<_K>(separator)
                }
                /// DafnyStandardLibraries-rs.dfy(11647,5)
                pub fn RepMerge(&self, merger: &Rc<dyn ::std::ops::Fn(&R, &R) -> R>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::RepMerge::<R>(self.apply(), merger)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11652,5)
                pub fn RepeatMerge(&self, merger: &Rc<dyn ::std::ops::Fn(&R, &R) -> R>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    self.RepMerge(merger)
                }
                /// DafnyStandardLibraries-rs.dfy(11657,5)
                pub fn RepSepMerge<_K: DafnyType>(&self, separator: &Rc<crate::Std::Parsers::StringBuilders::B<_K>>, merger: &Rc<dyn ::std::ops::Fn(&R, &R) -> R>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<R> {
                            apply: crate::Std::Parsers::StringParsers::_default::RepSepMerge::<R, _K>(self.apply(), separator.apply(), merger)
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11662,5)
                pub fn RepeatSeparatorMerge<_K: DafnyType>(&self, separator: &Rc<crate::Std::Parsers::StringBuilders::B<_K>>, merger: &Rc<dyn ::std::ops::Fn(&R, &R) -> R>) -> Rc<crate::Std::Parsers::StringBuilders::B<R>> {
                    self.RepSepMerge::<_K>(separator, merger)
                }
                /// DafnyStandardLibraries-rs.dfy(11667,5)
                pub fn Rep(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<R>> {
                            apply: crate::Std::Parsers::StringParsers::_default::ZeroOrMore::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11672,5)
                pub fn Repeat(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    self.Rep()
                }
                /// DafnyStandardLibraries-rs.dfy(11677,5)
                pub fn Rep1(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    Rc::new(crate::Std::Parsers::StringBuilders::B::B::<Sequence<R>> {
                            apply: crate::Std::Parsers::StringParsers::_default::OneOrMore::<R>(self.apply())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11682,5)
                pub fn RepeatAtLeastOnce(&self) -> Rc<crate::Std::Parsers::StringBuilders::B<Sequence<R>>> {
                    self.Rep1()
                }
                /// DafnyStandardLibraries-rs.dfy(11687,5)
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

            /// DafnyStandardLibraries-rs.dfy(11693,3)
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

            /// DafnyStandardLibraries-rs.dfy(11697,3)
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

        /// DafnyStandardLibraries-rs.dfy(12567,1)
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
                /// DafnyStandardLibraries-rs.dfy(12568,3)
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
                /// DafnyStandardLibraries-rs.dfy(12573,3)
                pub fn Space() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<DafnyChar>>> {
                    crate::Std::Parsers::StringParsers::_default::CharTest(&({
                            Rc::new(move |c: &DafnyChar| -> bool{
            string_of(" \t\r\n               　").contains(c)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), &string_of("space"))
                }
                /// DafnyStandardLibraries-rs.dfy(12578,3)
                pub fn WS() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Sequence<DafnyChar>>>> {
                    crate::Std::Parsers::StringParsers::_default::ZeroOrMore::<DafnyChar>(&crate::Std::Parsers::StringParsers::_default::Space())
                }
                /// DafnyStandardLibraries-rs.dfy(12583,3)
                pub fn Digit() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<DafnyChar>>> {
                    crate::Std::Parsers::StringParsers::_default::CharTest(&({
                            Rc::new(move |c: &DafnyChar| -> bool{
            string_of("0123456789").contains(c)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), &string_of("digit"))
                }
                /// DafnyStandardLibraries-rs.dfy(12588,3)
                pub fn DigitNumber() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<nat>>> {
                    crate::Std::Parsers::StringParsers::_default::Map::<DafnyChar, nat>(&crate::Std::Parsers::StringParsers::_default::Digit(), &({
                            Rc::new(move |c: &DafnyChar| -> nat{
            {
                let __pat_let10_0: DafnyInt = crate::Std::Parsers::StringParsers::_default::DigitToInt(c);
                {
                    let d: DafnyInt = __pat_let10_0.clone();
                    {
                        let __pat_let11_0: DafnyInt = if !(d.clone() < int!(0)) {
                                d.clone()
                            } else {
                                int!(0)
                            };
                        {
                            let n: nat = __pat_let11_0.clone();
                            n.clone()
                        }
                    }
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(12593,3)
                pub fn Nat() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<nat>>> {
                    crate::Std::Parsers::StringParsers::_default::Bind::<nat, nat>(&crate::Std::Parsers::StringParsers::_default::DigitNumber(), &({
                            Rc::new(move |result: &nat| -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<nat>>>{
            crate::Std::Parsers::StringParsers::_default::Rep::<nat, nat>(&crate::Std::Parsers::StringParsers::_default::DigitNumber(), &({
                    Rc::new(move |previous: &nat,c: &nat| -> nat{
            {
                let __pat_let12_0: DafnyInt = previous.clone() * int!(10) + c.clone();
                {
                    let r: nat = __pat_let12_0.clone();
                    r.clone()
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                }), result)
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(12598,3)
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
                /// DafnyStandardLibraries-rs.dfy(12603,3)
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
                /// DafnyStandardLibraries-rs.dfy(12647,3)
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
                /// DafnyStandardLibraries-rs.dfy(12707,3)
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
                                            let __pat_let13_0: DafnyChar = input.get(&int!(0));
                                            {
                                                let c: DafnyChar = __pat_let13_0.clone();
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
                /// DafnyStandardLibraries-rs.dfy(12712,3)
                pub fn DebugNameSummary(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                    string_of("[").concat(name).concat(&string_of("] ")).concat(&crate::Std::Parsers::StringParsers::_default::DebugSummary(input))
                }
                /// DafnyStandardLibraries-rs.dfy(12717,3)
                pub fn DebugSummaryInput(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                    string_of("> ").concat(&crate::Std::Parsers::StringParsers::_default::DebugNameSummary(name, input))
                }
                /// DafnyStandardLibraries-rs.dfy(12722,3)
                pub fn PrintDebugSummaryInput(name: &Sequence<DafnyChar>, input: &Sequence<DafnyChar>) -> () {
                    print!("{}", DafnyPrintWrapper(&crate::Std::Parsers::StringParsers::_default::DebugSummaryInput(name, input)));
                    return ();
                }
                /// DafnyStandardLibraries-rs.dfy(12727,3)
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
                /// DafnyStandardLibraries-rs.dfy(12735,3)
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
                /// DafnyStandardLibraries-rs.dfy(12749,3)
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
                                let __pat_let14_0: Rc<crate::Std::Parsers::StringParsers::CodeLocation> = crate::Std::Parsers::StringParsers::_default::ExtractLineCol(input, &pos);
                                {
                                    let output: Rc<crate::Std::Parsers::StringParsers::CodeLocation> = __pat_let14_0.clone();
                                    {
                                        let __pat_let15_0: Rc<crate::Std::Parsers::StringParsers::CodeLocation> = output.clone();
                                        {
                                            let line: nat = __pat_let15_0.lineNumber().clone();
                                            {
                                                let col: nat = __pat_let15_0.colNumber().clone();
                                                {
                                                    let lineStr: Sequence<DafnyChar> = __pat_let15_0.lineStr().clone();
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
                /// DafnyStandardLibraries-rs.dfy(12768,3)
                pub fn Apply<_T: DafnyType>(parser: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_T>>>, input: &Sequence<DafnyChar>) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_T>> {
                    parser(&crate::Std::Parsers::StringParsers::_default::ToInput(input))
                }
                /// DafnyStandardLibraries-rs.dfy(12773,3)
                pub fn ToInput(input: &Sequence<DafnyChar>) -> Input {
                    Rc::new(Slice::Slice::<DafnyChar> {
                            data: input.clone(),
                            start: int!(0),
                            end: input.cardinality()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(11733,3)
                pub fn IsRemaining(input: &Input, remaining: &Input) -> bool {
                    !(crate::Std::Parsers::InputString::_default::Length(input) < crate::Std::Parsers::InputString::_default::Length(remaining)) && crate::Std::Parsers::InputString::_default::Drop(input, &(crate::Std::Parsers::InputString::_default::Length(input) - crate::Std::Parsers::InputString::_default::Length(remaining))) == remaining.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(11747,3)
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
                /// DafnyStandardLibraries-rs.dfy(11752,3)
                pub fn Epsilon() -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<()>>> {
                    crate::Std::Parsers::StringParsers::_default::SucceedWith::<()>(&(()))
                }
                /// DafnyStandardLibraries-rs.dfy(11757,3)
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
                /// DafnyStandardLibraries-rs.dfy(11762,3)
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
                /// DafnyStandardLibraries-rs.dfy(11767,3)
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
                /// DafnyStandardLibraries-rs.dfy(11772,3)
                pub fn Bind<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&_L) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&_L) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let16_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let16_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<_R>()
                    } else {
                        {
                            let __pat_let17_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let leftResult: _L = __pat_let17_0.0.clone();
                                {
                                    let remaining: Input = __pat_let17_0.1.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11777,3)
                pub fn BindSucceeds<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&_L, &Input) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&_L, &Input) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let18_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let18_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<_R>()
                    } else {
                        {
                            let __pat_let19_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let leftResult: _L = __pat_let19_0.0.clone();
                                {
                                    let remaining: Input = __pat_let19_0.1.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11782,3)
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
                /// DafnyStandardLibraries-rs.dfy(11787,3)
                pub fn Map<_R: DafnyType, _U: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>, mappingFunc: &Rc<dyn ::std::ops::Fn(&_R) -> _U>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_U>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        let mappingFunc: Rc<dyn ::std::ops::Fn(&_R) -> _U> = mappingFunc.clone();
                        {
                            let mut underlying = underlying.clone();
                            let mut mappingFunc = mappingFunc.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_U>>{
            {
                let __pat_let20_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let20_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<_U>()
                    } else {
                        {
                            let __pat_let21_0: (_R, Input) = valueOrError0.Extract();
                            {
                                let result: _R = __pat_let21_0.0.clone();
                                {
                                    let remaining: Input = __pat_let21_0.1.clone();
                                    {
                                        let __pat_let22_0: _U = (&mappingFunc)(&result);
                                        {
                                            let u: _U = __pat_let22_0.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11792,3)
                pub fn Not<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<()>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        {
                            let mut underlying = underlying.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<()>>{
            {
                let __pat_let23_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                {
                    let l: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let23_0.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11797,3)
                pub fn And<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<(_L, _R)>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<(_L, _R)>>{
            {
                let __pat_let24_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let24_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<(_L, _R)>()
                    } else {
                        {
                            let __pat_let25_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let l: _L = __pat_let25_0.0.clone();
                                {
                                    let remainingLeft: Input = __pat_let25_0.1.clone();
                                    {
                                        let __pat_let26_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&right)(input);
                                        {
                                            let valueOrError1: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let26_0.clone();
                                            if valueOrError1.IsFailure() {
                                                valueOrError1.PropagateFailure::<(_L, _R)>()
                                            } else {
                                                {
                                                    let __pat_let27_0: (_R, Input) = valueOrError1.Extract();
                                                    {
                                                        let r: _R = __pat_let27_0.0.clone();
                                                        {
                                                            let remainingRight: Input = __pat_let27_0.1.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11802,3)
                pub fn Or<_R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let28_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&left)(input);
                {
                    let p: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let28_0.clone();
                    if !p.NeedsAlternative(input) {
                        p.clone()
                    } else {
                        {
                            let __pat_let29_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&right)(input);
                            {
                                let p2: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let29_0.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11807,3)
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
                /// DafnyStandardLibraries-rs.dfy(11817,3)
                pub fn Lookahead<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
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
                        {
                            let __pat_let33_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = p.clone();
                            {
                                let _dt__update__tmp_h1: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let33_0.clone();
                                {
                                    let __pat_let34_0: Input = input.clone();
                                    {
                                        let _dt__update_hremaining_h0: Input = __pat_let34_0.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11822,3)
                pub fn _q<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        {
                            let mut underlying = underlying.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>{
            {
                let __pat_let35_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                {
                    let p: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let35_0.clone();
                    if p.IsFailure() {
                        if p.IsFatal() {
                            p.clone()
                        } else {
                            {
                                let __pat_let36_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = p.clone();
                                {
                                    let _dt__update__tmp_h0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let36_0.clone();
                                    {
                                        let __pat_let37_0: Rc<crate::Std::Parsers::StringParsers::FailureData> = Rc::new(crate::Std::Parsers::StringParsers::FailureData::FailureData {
                                                    message: p.data().message().clone(),
                                                    remaining: input.clone(),
                                                    next: Rc::new(Option::None::<Rc<crate::Std::Parsers::StringParsers::FailureData>> {})
                                                });
                                        {
                                            let _dt__update_hdata_h0: Rc<crate::Std::Parsers::StringParsers::FailureData> = __pat_let37_0.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11827,3)
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
                /// DafnyStandardLibraries-rs.dfy(11844,3)
                pub fn Maybe<_R: DafnyType>(underlying: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<Option<_R>>>>> {
                    {
                        let underlying: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = underlying.clone();
                        {
                            let mut underlying = underlying.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<Option<_R>>>>{
            {
                let __pat_let38_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                {
                    let u: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let38_0.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11849,3)
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
                let __pat_let39_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let39_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<_T>()
                    } else {
                        {
                            let __pat_let40_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let l: _L = __pat_let40_0.0.clone();
                                {
                                    let remaining: Input = __pat_let40_0.1.clone();
                                    {
                                        let __pat_let41_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&right)(&remaining);
                                        {
                                            let valueOrError1: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let41_0.clone();
                                            if valueOrError1.IsFailure() {
                                                valueOrError1.PropagateFailure::<_T>()
                                            } else {
                                                {
                                                    let __pat_let42_0: (_R, Input) = valueOrError1.Extract();
                                                    {
                                                        let r: _R = __pat_let42_0.0.clone();
                                                        {
                                                            let remaining2: Input = __pat_let42_0.1.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11854,3)
                pub fn Concat<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<(_L, _R)>>> {
                    {
                        let left: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> = left.clone();
                        let right: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = right.clone();
                        {
                            let mut left = left.clone();
                            let mut right = right.clone();
                            Rc::new(move |input: &Input| -> Rc<crate::Std::Parsers::StringParsers::ParseResult<(_L, _R)>>{
            {
                let __pat_let43_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = (&left)(input);
                {
                    let valueOrError0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>> = __pat_let43_0.clone();
                    if valueOrError0.IsFailure() {
                        valueOrError0.PropagateFailure::<(_L, _R)>()
                    } else {
                        {
                            let __pat_let44_0: (_L, Input) = valueOrError0.Extract();
                            {
                                let l: _L = __pat_let44_0.0.clone();
                                {
                                    let remaining: Input = __pat_let44_0.1.clone();
                                    {
                                        let __pat_let45_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&right)(&remaining);
                                        {
                                            let valueOrError1: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let45_0.clone();
                                            if valueOrError1.IsFailure() {
                                                valueOrError1.PropagateFailure::<(_L, _R)>()
                                            } else {
                                                {
                                                    let __pat_let46_0: (_R, Input) = valueOrError1.Extract();
                                                    {
                                                        let r: _R = __pat_let46_0.0.clone();
                                                        {
                                                            let remaining2: Input = __pat_let46_0.1.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11859,3)
                pub fn ConcatKeepRight<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> {
                    crate::Std::Parsers::StringParsers::_default::ConcatMap::<_L, _R, _R>(left, right, &({
                            Rc::new(move |l: &_L,r: &_R| -> _R{
            r.clone()
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(11864,3)
                pub fn ConcatKeepLeft<_L: DafnyType, _R: DafnyType>(left: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>>, right: &Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_L>>> {
                    crate::Std::Parsers::StringParsers::_default::ConcatMap::<_L, _R, _L>(left, right, &({
                            Rc::new(move |l: &_L,r: &_R| -> _L{
            l.clone()
        }) as Rc<dyn ::std::ops::Fn(&_, &_) -> _>
                        }))
                }
                /// DafnyStandardLibraries-rs.dfy(11869,3)
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
                let __pat_let47_0: _D = (&onEnter)(&name, input);
                {
                    let debugData: _D = __pat_let47_0.clone();
                    {
                        let __pat_let48_0: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = (&underlying)(input);
                        {
                            let output: Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>> = __pat_let48_0.clone();
                            {
                                let __pat_let49_0: () = (&onExit)(&name, &debugData, &output);
                                {
                                    let _v16: () = __pat_let49_0.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11874,3)
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
                /// DafnyStandardLibraries-rs.dfy(11879,3)
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
                /// DafnyStandardLibraries-rs.dfy(11884,3)
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
                /// DafnyStandardLibraries-rs.dfy(11889,3)
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
                /// DafnyStandardLibraries-rs.dfy(11894,3)
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
                /// DafnyStandardLibraries-rs.dfy(11899,3)
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
                /// DafnyStandardLibraries-rs.dfy(11904,3)
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
                /// DafnyStandardLibraries-rs.dfy(11920,3)
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
                /// DafnyStandardLibraries-rs.dfy(11925,3)
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
                /// DafnyStandardLibraries-rs.dfy(11935,3)
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
                /// DafnyStandardLibraries-rs.dfy(11942,3)
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
                /// DafnyStandardLibraries-rs.dfy(11947,3)
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
                                let mut ___mcc_h0: _R = _source0._h19().clone();
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
                                let mut ___mcc_h1: Rc<dyn ::std::ops::Fn(&_R) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<_R>>>>>> = _source0._h20().clone();
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
                    let __pat_let50_0: (_R, Input) = p.Extract();
                    {
                        let r: _R = __pat_let50_0.0.clone();
                        {
                            let remaining2: Input = __pat_let50_0.1.clone();
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
                /// DafnyStandardLibraries-rs.dfy(11953,3)
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
                /// DafnyStandardLibraries-rs.dfy(11958,3)
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
                let __pat_let51_0: Rc<dyn ::std::ops::Fn(&Rc<Slice<DafnyChar>>) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = if !underlying.keys().contains(_fun_k) {
                        crate::Std::Parsers::StringParsers::_default::FailWith::<_R>(&_fun_k.concat(&string_of(" not defined")), &Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {}))
                    } else {
                        {
                            let __pat_let52_0: Rc<crate::Std::Parsers::StringParsers::RecursiveDef<_R>> = underlying.get(_fun_k);
                            {
                                let _orderFun_k: nat = __pat_let52_0.order().clone();
                                {
                                    let _definitionFun_k: Rc<dyn ::std::ops::Fn(&Rc<dyn ::std::ops::Fn(&Sequence<DafnyChar>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>>) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>>> = __pat_let52_0.definition().clone();
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
                    let p: Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_R>>> = __pat_let51_0.clone();
                    p.clone()
                }
            }
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                                }
                            };
                        (&(&definitionFun)(&callback))(input)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(11967,3)
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
                /// DafnyStandardLibraries-rs.dfy(11972,3)
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
                /// DafnyStandardLibraries-rs.dfy(11999,3)
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

            /// DafnyStandardLibraries-rs.dfy(12791,3)
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

            /// DafnyStandardLibraries-rs.dfy(12793,3)
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

            /// DafnyStandardLibraries-rs.dfy(12037,3)
            #[derive(Clone)]
            pub enum FailureData {
                FailureData {
                    message: Sequence<DafnyChar>,
                    remaining: Input,
                    next: Rc<Option<Rc<crate::Std::Parsers::StringParsers::FailureData>>>
                }
            }

            impl FailureData {
                /// DafnyStandardLibraries-rs.dfy(12038,5)
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

            /// DafnyStandardLibraries-rs.dfy(12047,3)
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

            /// DafnyStandardLibraries-rs.dfy(12049,3)
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
                /// DafnyStandardLibraries-rs.dfy(12050,5)
                pub fn Remaining(&self) -> Input {
                    if matches!((&Rc::new(self.clone())).as_ref(), ParseSuccess{ .. }) {
                        self.remaining().clone()
                    } else {
                        self.data().remaining().clone()
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(12058,5)
                pub fn IsFailure(&self) -> bool {
                    matches!((&Rc::new(self.clone())).as_ref(), ParseFailure{ .. })
                }
                /// DafnyStandardLibraries-rs.dfy(12063,5)
                pub fn IsFatalFailure(&self) -> bool {
                    matches!((&Rc::new(self.clone())).as_ref(), ParseFailure{ .. }) && self.level().clone() == Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {})
                }
                /// DafnyStandardLibraries-rs.dfy(12069,5)
                pub fn IsFatal(&self) -> bool {
                    self.level().clone() == Rc::new(crate::Std::Parsers::StringParsers::FailureLevel::Fatal {})
                }
                /// DafnyStandardLibraries-rs.dfy(12075,5)
                pub fn PropagateFailure<_U: DafnyType>(&self) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<_U>> {
                    Rc::new(crate::Std::Parsers::StringParsers::ParseResult::ParseFailure::<_U> {
                            level: self.level().clone(),
                            data: self.data().clone()
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12081,5)
                pub fn Extract(&self) -> (R, Input) {
                    (
                        self.result().clone(),
                        self.remaining().clone()
                    )
                }
                /// DafnyStandardLibraries-rs.dfy(12087,5)
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
                /// DafnyStandardLibraries-rs.dfy(12096,5)
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
                /// DafnyStandardLibraries-rs.dfy(12105,5)
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

            /// DafnyStandardLibraries-rs.dfy(12113,3)
            #[derive(Clone)]
            pub enum SeqB<A: DafnyType> {
                SeqBCons {
                    last: A,
                    init: Rc<crate::Std::Parsers::StringParsers::SeqB<A>>
                },
                SeqBNil {}
            }

            impl<A: DafnyType> SeqB<A> {
                /// DafnyStandardLibraries-rs.dfy(12114,5)
                pub fn Append(&self, elem: &A) -> Rc<crate::Std::Parsers::StringParsers::SeqB<A>> {
                    Rc::new(crate::Std::Parsers::StringParsers::SeqB::SeqBCons::<A> {
                            last: elem.clone(),
                            init: Rc::new(self.clone())
                        })
                }
                /// DafnyStandardLibraries-rs.dfy(12119,5)
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
                /// DafnyStandardLibraries-rs.dfy(12127,5)
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

            /// DafnyStandardLibraries-rs.dfy(12159,3)
            #[derive(Clone)]
            pub enum RecursiveNoStackResult<R: DafnyType> {
                RecursiveReturn {
                    _h19: R
                },
                RecursiveContinue {
                    _h20: Rc<dyn ::std::ops::Fn(&R) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<R>>>>>>
                }
            }

            impl<R: DafnyType> RecursiveNoStackResult<R> {
                /// Gets the field _h19 for all enum members which have it
                pub fn _h19(&self) -> &R {
                    match self {
                        RecursiveNoStackResult::RecursiveReturn{_h19, } => _h19,
                        RecursiveNoStackResult::RecursiveContinue{_h20, } => panic!("field does not exist on this variant"),
                    }
                }
                /// Gets the field _h20 for all enum members which have it
                pub fn _h20(&self) -> &Rc<dyn ::std::ops::Fn(&R) -> Rc<dyn ::std::ops::Fn(&Input) -> Rc<crate::Std::Parsers::StringParsers::ParseResult<Rc<crate::Std::Parsers::StringParsers::RecursiveNoStackResult<R>>>>>> {
                    match self {
                        RecursiveNoStackResult::RecursiveReturn{_h19, } => panic!("field does not exist on this variant"),
                        RecursiveNoStackResult::RecursiveContinue{_h20, } => _h20,
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
                        RecursiveNoStackResult::RecursiveReturn{_h19, } => {
                            write!(_formatter, "Std.Parsers.StringParsers.RecursiveNoStackResult.RecursiveReturn(")?;
                            DafnyPrint::fmt_print(_h19, _formatter, false)?;
                            write!(_formatter, ")")?;
                            Ok(())
                        },
                        RecursiveNoStackResult::RecursiveContinue{_h20, } => {
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

            /// DafnyStandardLibraries-rs.dfy(12163,3)
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

    /// DafnyStandardLibraries-rs.dfy(12796,1)
    pub mod Relations {
        
    }

    /// DafnyStandardLibraries-rs.dfy(12932,1)
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
            /// DafnyStandardLibraries-rs.dfy(12934,3)
            pub fn OfNat(n: &nat) -> Sequence<DafnyChar> {
                crate::Std::Strings::DecimalConversion::_default::OfNat(n)
            }
            /// DafnyStandardLibraries-rs.dfy(12941,3)
            pub fn OfInt(n: &DafnyInt) -> Sequence<DafnyChar> {
                crate::Std::Strings::DecimalConversion::_default::OfInt(n, &DafnyChar(char::from_u32(45).unwrap()))
            }
            /// DafnyStandardLibraries-rs.dfy(12947,3)
            pub fn ToNat(str: &Sequence<DafnyChar>) -> nat {
                crate::Std::Strings::DecimalConversion::_default::ToNat(str)
            }
            /// DafnyStandardLibraries-rs.dfy(12955,3)
            pub fn ToInt(str: &Sequence<DafnyChar>) -> DafnyInt {
                crate::Std::Strings::DecimalConversion::_default::ToInt(str, &DafnyChar(char::from_u32(45).unwrap()))
            }
            /// DafnyStandardLibraries-rs.dfy(12962,3)
            pub fn EscapeQuotes(str: &Sequence<DafnyChar>) -> Sequence<DafnyChar> {
                crate::Std::Strings::CharStrEscaping::_default::Escape(str, &set!{DafnyChar(char::from_u32(34).unwrap()), DafnyChar(char::from_u32(39).unwrap())}, &DafnyChar(char::from_u32(92).unwrap()))
            }
            /// DafnyStandardLibraries-rs.dfy(12967,3)
            pub fn UnescapeQuotes(str: &Sequence<DafnyChar>) -> Rc<Option<Sequence<DafnyChar>>> {
                crate::Std::Strings::CharStrEscaping::_default::Unescape(str, &DafnyChar(char::from_u32(92).unwrap()))
            }
            /// DafnyStandardLibraries-rs.dfy(12972,3)
            pub fn OfBool(b: bool) -> Sequence<DafnyChar> {
                if b {
                    string_of("true")
                } else {
                    string_of("false")
                }
            }
            /// DafnyStandardLibraries-rs.dfy(12980,3)
            pub fn OfChar(c: &DafnyChar) -> Sequence<DafnyChar> {
                seq![c.clone()]
            }
        }

        /// DafnyStandardLibraries-rs.dfy(13179,3)
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
                /// DafnyStandardLibraries-rs.dfy(13112,5)
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
                /// DafnyStandardLibraries-rs.dfy(13122,5)
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

        /// DafnyStandardLibraries-rs.dfy(13165,3)
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
                /// DafnyStandardLibraries-rs.dfy(13002,5)
                pub fn BASE() -> nat {
                    crate::Std::Strings::DecimalConversion::_default::base()
                }
                /// DafnyStandardLibraries-rs.dfy(13007,5)
                pub fn IsDigitChar(c: &DafnyChar) -> bool {
                    crate::Std::Strings::DecimalConversion::_default::charToDigit().contains(c)
                }
                /// DafnyStandardLibraries-rs.dfy(13012,5)
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
                /// DafnyStandardLibraries-rs.dfy(13022,5)
                pub fn OfNat(n: &nat) -> Sequence<DafnyChar> {
                    if n.clone() == int!(0) {
                        seq![crate::Std::Strings::DecimalConversion::_default::chars().get(&int!(0))]
                    } else {
                        crate::Std::Strings::DecimalConversion::_default::OfDigits(&crate::Std::Strings::DecimalConversion::_default::FromNat(n))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13032,5)
                pub fn IsNumberStr(str: &Sequence<DafnyChar>, minus: &DafnyChar) -> bool {
                    !(!(str.clone().to_array().len() == 0)) || (str.get(&int!(0)) == minus.clone() || crate::Std::Strings::DecimalConversion::_default::charToDigit().contains(&str.get(&int!(0)))) && Itertools::unique((&str.drop(&int!(1))).iter()).all(({
                            let mut str = str.clone();
                            Rc::new(move |__forall_var_0: DafnyChar| -> bool{
            let mut c: DafnyChar = __forall_var_0.clone();
            !str.drop(&int!(1)).contains(&c) || crate::Std::Strings::DecimalConversion::_default::IsDigitChar(&c)
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                        }).as_ref())
                }
                /// DafnyStandardLibraries-rs.dfy(13040,5)
                pub fn OfInt(n: &DafnyInt, minus: &DafnyChar) -> Sequence<DafnyChar> {
                    if !(n.clone() < int!(0)) {
                        crate::Std::Strings::DecimalConversion::_default::OfNat(n)
                    } else {
                        seq![minus.clone()].concat(&crate::Std::Strings::DecimalConversion::_default::OfNat(&(int!(0) - n.clone())))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13050,5)
                pub fn ToNat(str: &Sequence<DafnyChar>) -> nat {
                    if str.clone().to_array().len() == 0 {
                        int!(0)
                    } else {
                        let mut c: DafnyChar = str.get(&(str.cardinality() - int!(1)));
                        crate::Std::Strings::DecimalConversion::_default::ToNat(&str.take(&(str.cardinality() - int!(1)))) * crate::Std::Strings::DecimalConversion::_default::base() + crate::Std::Strings::DecimalConversion::_default::charToDigit().get(&c)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13090,5)
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
                /// DafnyStandardLibraries-rs.dfy(13167,5)
                pub fn DIGITS() -> Sequence<DafnyChar> {
                    string_of("0123456789")
                }
                /// DafnyStandardLibraries-rs.dfy(13168,5)
                pub fn chars() -> Sequence<DafnyChar> {
                    crate::Std::Strings::DecimalConversion::_default::DIGITS()
                }
                /// DafnyStandardLibraries-rs.dfy(12996,5)
                pub fn base() -> DafnyInt {
                    crate::Std::Strings::DecimalConversion::_default::chars().cardinality()
                }
                /// DafnyStandardLibraries-rs.dfy(13169,5)
                pub fn charToDigit() -> Map<DafnyChar, crate::Std::Strings::DecimalConversion::digit> {
                    map![DafnyChar(char::from_u32(48).unwrap()) => int!(0), DafnyChar(char::from_u32(49).unwrap()) => int!(1), DafnyChar(char::from_u32(50).unwrap()) => int!(2), DafnyChar(char::from_u32(51).unwrap()) => int!(3), DafnyChar(char::from_u32(52).unwrap()) => int!(4), DafnyChar(char::from_u32(53).unwrap()) => int!(5), DafnyChar(char::from_u32(54).unwrap()) => int!(6), DafnyChar(char::from_u32(55).unwrap()) => int!(7), DafnyChar(char::from_u32(56).unwrap()) => int!(8), DafnyChar(char::from_u32(57).unwrap()) => int!(9)]
                }
            }

            /// DafnyStandardLibraries-rs.dfy(13106,5)
            pub type CharSeq = Sequence<DafnyChar>;

            /// DafnyStandardLibraries-rs.dfy(3285,3)
            pub type digit = DafnyInt;
        }

        /// DafnyStandardLibraries-rs.dfy(13153,3)
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
                /// DafnyStandardLibraries-rs.dfy(13002,5)
                pub fn BASE() -> nat {
                    crate::Std::Strings::HexConversion::_default::base()
                }
                /// DafnyStandardLibraries-rs.dfy(13007,5)
                pub fn IsDigitChar(c: &DafnyChar) -> bool {
                    crate::Std::Strings::HexConversion::_default::charToDigit().contains(c)
                }
                /// DafnyStandardLibraries-rs.dfy(13012,5)
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
                /// DafnyStandardLibraries-rs.dfy(13022,5)
                pub fn OfNat(n: &nat) -> Sequence<DafnyChar> {
                    if n.clone() == int!(0) {
                        seq![crate::Std::Strings::HexConversion::_default::chars().get(&int!(0))]
                    } else {
                        crate::Std::Strings::HexConversion::_default::OfDigits(&crate::Std::Strings::HexConversion::_default::FromNat(n))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13032,5)
                pub fn IsNumberStr(str: &Sequence<DafnyChar>, minus: &DafnyChar) -> bool {
                    !(!(str.clone().to_array().len() == 0)) || (str.get(&int!(0)) == minus.clone() || crate::Std::Strings::HexConversion::_default::charToDigit().contains(&str.get(&int!(0)))) && Itertools::unique((&str.drop(&int!(1))).iter()).all(({
                            let mut str = str.clone();
                            Rc::new(move |__forall_var_0: DafnyChar| -> bool{
            let mut c: DafnyChar = __forall_var_0.clone();
            !str.drop(&int!(1)).contains(&c) || crate::Std::Strings::HexConversion::_default::IsDigitChar(&c)
        }) as Rc<dyn ::std::ops::Fn(_) -> _>
                        }).as_ref())
                }
                /// DafnyStandardLibraries-rs.dfy(13040,5)
                pub fn OfInt(n: &DafnyInt, minus: &DafnyChar) -> Sequence<DafnyChar> {
                    if !(n.clone() < int!(0)) {
                        crate::Std::Strings::HexConversion::_default::OfNat(n)
                    } else {
                        seq![minus.clone()].concat(&crate::Std::Strings::HexConversion::_default::OfNat(&(int!(0) - n.clone())))
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13050,5)
                pub fn ToNat(str: &Sequence<DafnyChar>) -> nat {
                    if str.clone().to_array().len() == 0 {
                        int!(0)
                    } else {
                        let mut c: DafnyChar = str.get(&(str.cardinality() - int!(1)));
                        crate::Std::Strings::HexConversion::_default::ToNat(&str.take(&(str.cardinality() - int!(1)))) * crate::Std::Strings::HexConversion::_default::base() + crate::Std::Strings::HexConversion::_default::charToDigit().get(&c)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13090,5)
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
                /// DafnyStandardLibraries-rs.dfy(13155,5)
                pub fn HEX_DIGITS() -> Sequence<DafnyChar> {
                    string_of("0123456789ABCDEF")
                }
                /// DafnyStandardLibraries-rs.dfy(13156,5)
                pub fn chars() -> Sequence<DafnyChar> {
                    crate::Std::Strings::HexConversion::_default::HEX_DIGITS()
                }
                /// DafnyStandardLibraries-rs.dfy(12996,5)
                pub fn base() -> DafnyInt {
                    crate::Std::Strings::HexConversion::_default::chars().cardinality()
                }
                /// DafnyStandardLibraries-rs.dfy(13157,5)
                pub fn charToDigit() -> Map<DafnyChar, crate::Std::Strings::HexConversion::digit> {
                    map![DafnyChar(char::from_u32(48).unwrap()) => int!(0), DafnyChar(char::from_u32(49).unwrap()) => int!(1), DafnyChar(char::from_u32(50).unwrap()) => int!(2), DafnyChar(char::from_u32(51).unwrap()) => int!(3), DafnyChar(char::from_u32(52).unwrap()) => int!(4), DafnyChar(char::from_u32(53).unwrap()) => int!(5), DafnyChar(char::from_u32(54).unwrap()) => int!(6), DafnyChar(char::from_u32(55).unwrap()) => int!(7), DafnyChar(char::from_u32(56).unwrap()) => int!(8), DafnyChar(char::from_u32(57).unwrap()) => int!(9), DafnyChar(char::from_u32(97).unwrap()) => int!(10), DafnyChar(char::from_u32(98).unwrap()) => int!(11), DafnyChar(char::from_u32(99).unwrap()) => int!(12), DafnyChar(char::from_u32(100).unwrap()) => int!(13), DafnyChar(char::from_u32(101).unwrap()) => int!(14), DafnyChar(char::from_u32(102).unwrap()) => int!(15), DafnyChar(char::from_u32(65).unwrap()) => int!(10), DafnyChar(char::from_u32(66).unwrap()) => int!(11), DafnyChar(char::from_u32(67).unwrap()) => int!(12), DafnyChar(char::from_u32(68).unwrap()) => int!(13), DafnyChar(char::from_u32(69).unwrap()) => int!(14), DafnyChar(char::from_u32(70).unwrap()) => int!(15)]
                }
            }

            /// DafnyStandardLibraries-rs.dfy(13106,5)
            pub type CharSeq = Sequence<DafnyChar>;

            /// DafnyStandardLibraries-rs.dfy(3285,3)
            pub type digit = DafnyInt;
        }
    }

    /// DafnyStandardLibraries-rs.dfy(13216,1)
    pub mod Unicode {
        /// DafnyStandardLibraries-rs.dfy(13184,1)
        pub mod Base {
            pub use ::dafny_runtime::truncate;
            pub use ::dafny_runtime::int;
            pub use ::dafny_runtime::Set;
            pub use ::dafny_runtime::set;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(13191,3)
                pub fn IsInAssignedPlane(i: crate::Std::Unicode::Base::CodePoint) -> bool {
                    let mut plane: u8 = (i >> truncate!(int!(16), u8)) as u8;
                    crate::Std::Unicode::Base::_default::ASSIGNED_PLANES().contains(&plane)
                }
                /// DafnyStandardLibraries-rs.dfy(13185,3)
                pub fn HIGH_SURROGATE_MIN() -> crate::Std::Unicode::Base::CodePoint {
                    55296 as u32
                }
                /// DafnyStandardLibraries-rs.dfy(13186,3)
                pub fn HIGH_SURROGATE_MAX() -> crate::Std::Unicode::Base::CodePoint {
                    56319 as u32
                }
                /// DafnyStandardLibraries-rs.dfy(13187,3)
                pub fn LOW_SURROGATE_MIN() -> crate::Std::Unicode::Base::CodePoint {
                    56320 as u32
                }
                /// DafnyStandardLibraries-rs.dfy(13188,3)
                pub fn LOW_SURROGATE_MAX() -> crate::Std::Unicode::Base::CodePoint {
                    57343 as u32
                }
                /// DafnyStandardLibraries-rs.dfy(13189,3)
                pub fn ASSIGNED_PLANES() -> Set<u8> {
                    set!{0 as u8, 1 as u8, 2 as u8, 3 as u8, 14 as u8, 15 as u8, 16 as u8}
                }
            }

            /// DafnyStandardLibraries-rs.dfy(13197,3)
            pub type CodePoint = u32;

            /// DafnyStandardLibraries-rs.dfy(13200,3)
            pub type HighSurrogateCodePoint = u32;

            /// An element of HighSurrogateCodePoint
            pub fn __init_HighSurrogateCodePoint() -> u32 {
                crate::Std::Unicode::Base::_default::HIGH_SURROGATE_MIN()
            }

            /// DafnyStandardLibraries-rs.dfy(13204,3)
            pub type LowSurrogateCodePoint = u32;

            /// An element of LowSurrogateCodePoint
            pub fn __init_LowSurrogateCodePoint() -> u32 {
                crate::Std::Unicode::Base::_default::LOW_SURROGATE_MIN()
            }

            /// DafnyStandardLibraries-rs.dfy(13208,3)
            pub type ScalarValue = u32;

            /// DafnyStandardLibraries-rs.dfy(13211,3)
            pub type AssignedCodePoint = u32;
        }

        /// DafnyStandardLibraries-rs.dfy(13484,1)
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
                /// DafnyStandardLibraries-rs.dfy(13504,3)
                pub fn CharAsUnicodeScalarValue(c: &DafnyChar) -> ScalarValue {
                    truncate!(int!(c.clone().0), u32)
                }
                /// DafnyStandardLibraries-rs.dfy(13510,3)
                pub fn CharFromUnicodeScalarValue(sv: ScalarValue) -> DafnyChar {
                    DafnyChar(char::from_u32(<u32 as NumCast>::from(int!(sv)).unwrap()).unwrap())
                }
                /// DafnyStandardLibraries-rs.dfy(13516,3)
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
                /// DafnyStandardLibraries-rs.dfy(13525,3)
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
                /// DafnyStandardLibraries-rs.dfy(13531,3)
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
                /// DafnyStandardLibraries-rs.dfy(13540,3)
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
                /// DafnyStandardLibraries-rs.dfy(13459,3)
                pub fn ASCIIToUTF8(s: &Sequence<DafnyChar>) -> Sequence<u8> {
                    crate::Std::Collections::Seq::_default::Map::<DafnyChar, u8>(&({
                            Rc::new(move |c: &DafnyChar| -> u8{
            c.clone().0 as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), s)
                }
                /// DafnyStandardLibraries-rs.dfy(13469,3)
                pub fn ASCIIToUTF16(s: &Sequence<DafnyChar>) -> Sequence<u16> {
                    crate::Std::Collections::Seq::_default::Map::<DafnyChar, u16>(&({
                            Rc::new(move |c: &DafnyChar| -> u16{
            c.clone().0 as u16
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), s)
                }
            }
        }

        /// DafnyStandardLibraries-rs.dfy(13553,1)
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
                /// DafnyStandardLibraries-rs.dfy(13554,3)
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
                /// DafnyStandardLibraries-rs.dfy(13566,3)
                pub fn IsWellFormedSingleCodeUnitSequence(s: &Sequence<u16>) -> bool {
                    let mut firstWord: u16 = s.get(&int!(0));
                    !(firstWord < 0 as u16) && !((55295 as u16) < firstWord) || !(firstWord < 57344 as u16) && !((65535 as u16) < firstWord)
                }
                /// DafnyStandardLibraries-rs.dfy(13573,3)
                pub fn IsWellFormedDoubleCodeUnitSequence(s: &Sequence<u16>) -> bool {
                    let mut firstWord: u16 = s.get(&int!(0));
                    let mut secondWord: u16 = s.get(&int!(1));
                    !(firstWord < 55296 as u16) && !((56319 as u16) < firstWord) && (!(secondWord < 56320 as u16) && !((57343 as u16) < secondWord))
                }
                /// DafnyStandardLibraries-rs.dfy(13583,3)
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
                /// DafnyStandardLibraries-rs.dfy(13596,3)
                pub fn EncodeScalarValue(v: ScalarValue) -> crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq {
                    if !(v < 0 as u32) && !((55295 as u32) < v) || !(v < 57344 as u32) && !((65535 as u32) < v) {
                        crate::Std::Unicode::Utf16EncodingForm::_default::EncodeScalarValueSingleWord(v)
                    } else {
                        crate::Std::Unicode::Utf16EncodingForm::_default::EncodeScalarValueDoubleWord(v)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13604,3)
                pub fn EncodeScalarValueSingleWord(v: ScalarValue) -> crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq {
                    let mut firstWord: u16 = v as u16;
                    seq![firstWord]
                }
                /// DafnyStandardLibraries-rs.dfy(13613,3)
                pub fn EncodeScalarValueDoubleWord(v: ScalarValue) -> crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq {
                    let mut x2: u16 = (v & 1023 as u32) as u16;
                    let mut x1: u8 = ((v & 64512 as u32) >> truncate!(int!(10), u8)) as u8;
                    let mut u: u8 = ((v & 2031616 as u32) >> truncate!(int!(16), u8)) as u8;
                    let mut w: u8 = u.wrapping_sub(1 as u8);
                    let mut firstWord: u16 = 55296 as u16 | (w as u16) << truncate!(int!(6), u8) | x1 as u16;
                    let mut secondWord: u16 = 56320 as u16 | x2;
                    seq![firstWord, secondWord]
                }
                /// DafnyStandardLibraries-rs.dfy(13627,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequence(m: &crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    if m.cardinality() == int!(1) {
                        crate::Std::Unicode::Utf16EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m)
                    } else {
                        crate::Std::Unicode::Utf16EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m)
                    }
                }
                /// DafnyStandardLibraries-rs.dfy(13635,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m: &crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstWord: u16 = m.get(&int!(0));
                    let mut x: u16 = firstWord;
                    x as u32
                }
                /// DafnyStandardLibraries-rs.dfy(13646,3)
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
                /// DafnyStandardLibraries-rs.dfy(13268,3)
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
                /// DafnyStandardLibraries-rs.dfy(13294,3)
                pub fn PartitionCodeUnitSequence(s: &crate::Std::Unicode::Utf16EncodingForm::WellFormedCodeUnitSeq) -> Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq> {
                    crate::Std::Unicode::Utf16EncodingForm::_default::PartitionCodeUnitSequenceChecked(s).Extract()
                }
                /// DafnyStandardLibraries-rs.dfy(13322,3)
                pub fn IsWellFormedCodeUnitSequence(s: &Sequence<u16>) -> bool {
                    matches!((&crate::Std::Unicode::Utf16EncodingForm::_default::PartitionCodeUnitSequenceChecked(s)).as_ref(), Success{ .. })
                }
                /// DafnyStandardLibraries-rs.dfy(13363,3)
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
                /// DafnyStandardLibraries-rs.dfy(13382,3)
                pub fn DecodeCodeUnitSequence(s: &crate::Std::Unicode::Utf16EncodingForm::WellFormedCodeUnitSeq) -> Sequence<ScalarValue> {
                    let mut parts: Sequence<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq> = crate::Std::Unicode::Utf16EncodingForm::_default::PartitionCodeUnitSequence(s);
                    let mut vs: Sequence<ScalarValue> = crate::Std::Collections::Seq::_default::MapPartialFunction::<crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq, ScalarValue>(&(Rc::new(move |x0: &crate::Std::Unicode::Utf16EncodingForm::MinimalWellFormedCodeUnitSeq| crate::Std::Unicode::Utf16EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequence(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>), &parts);
                    vs.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(13399,3)
                pub fn DecodeErrorMessage(index: &DafnyInt) -> Sequence<DafnyChar> {
                    string_of("Could not decode byte at index ").concat(&crate::Std::Strings::_default::OfInt(index))
                }
                /// DafnyStandardLibraries-rs.dfy(13404,3)
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

            /// DafnyStandardLibraries-rs.dfy(13445,3)
            pub type WellFormedCodeUnitSeq = Sequence<u16>;

            /// An element of WellFormedCodeUnitSeq
            pub fn __init_WellFormedCodeUnitSeq() -> Sequence<u16> {
                seq![] as Sequence<u16>
            }

            /// DafnyStandardLibraries-rs.dfy(13449,3)
            pub type MinimalWellFormedCodeUnitSeq = Sequence<u16>;
        }

        /// DafnyStandardLibraries-rs.dfy(13666,1)
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
                /// DafnyStandardLibraries-rs.dfy(13667,3)
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
                /// DafnyStandardLibraries-rs.dfy(13689,3)
                pub fn IsWellFormedSingleCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    let mut firstByte: u8 = s.get(&int!(0));
                    true && (!(firstByte < 0 as u8) && !((127 as u8) < firstByte))
                }
                /// DafnyStandardLibraries-rs.dfy(13697,3)
                pub fn IsWellFormedDoubleCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    let mut firstByte: u8 = s.get(&int!(0));
                    let mut secondByte: u8 = s.get(&int!(1));
                    !(firstByte < 194 as u8) && !((223 as u8) < firstByte) && (!(secondByte < 128 as u8) && !((191 as u8) < secondByte))
                }
                /// DafnyStandardLibraries-rs.dfy(13707,3)
                pub fn IsWellFormedTripleCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    let mut firstByte: u8 = s.get(&int!(0));
                    let mut secondByte: u8 = s.get(&int!(1));
                    let mut thirdByte: u8 = s.get(&int!(2));
                    (firstByte == 224 as u8 && (!(secondByte < 160 as u8) && !((191 as u8) < secondByte)) || !(firstByte < 225 as u8) && !((236 as u8) < firstByte) && (!(secondByte < 128 as u8) && !((191 as u8) < secondByte)) || firstByte == 237 as u8 && (!(secondByte < 128 as u8) && !((159 as u8) < secondByte)) || !(firstByte < 238 as u8) && !((239 as u8) < firstByte) && (!(secondByte < 128 as u8) && !((191 as u8) < secondByte))) && (!(thirdByte < 128 as u8) && !((191 as u8) < thirdByte))
                }
                /// DafnyStandardLibraries-rs.dfy(13718,3)
                pub fn IsWellFormedQuadrupleCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    let mut firstByte: u8 = s.get(&int!(0));
                    let mut secondByte: u8 = s.get(&int!(1));
                    let mut thirdByte: u8 = s.get(&int!(2));
                    let mut fourthByte: u8 = s.get(&int!(3));
                    (firstByte == 240 as u8 && (!(secondByte < 144 as u8) && !((191 as u8) < secondByte)) || !(firstByte < 241 as u8) && !((243 as u8) < firstByte) && (!(secondByte < 128 as u8) && !((191 as u8) < secondByte)) || firstByte == 244 as u8 && (!(secondByte < 128 as u8) && !((143 as u8) < secondByte))) && (!(thirdByte < 128 as u8) && !((191 as u8) < thirdByte)) && (!(fourthByte < 128 as u8) && !((191 as u8) < fourthByte))
                }
                /// DafnyStandardLibraries-rs.dfy(13731,3)
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
                /// DafnyStandardLibraries-rs.dfy(13745,3)
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
                /// DafnyStandardLibraries-rs.dfy(13757,3)
                pub fn EncodeScalarValueSingleByte(v: ScalarValue) -> crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq {
                    let mut x: u8 = (v & 127 as u32) as u8;
                    let mut firstByte: u8 = x;
                    seq![firstByte]
                }
                /// DafnyStandardLibraries-rs.dfy(13767,3)
                pub fn EncodeScalarValueDoubleByte(v: ScalarValue) -> Sequence<u8> {
                    let mut x: u8 = (v & 63 as u32) as u8;
                    let mut y: u8 = ((v & 1984 as u32) >> truncate!(int!(6), u8)) as u8;
                    let mut firstByte: u8 = 192 as u8 | y;
                    let mut secondByte: u8 = 128 as u8 | x;
                    seq![firstByte, secondByte]
                }
                /// DafnyStandardLibraries-rs.dfy(13779,3)
                pub fn EncodeScalarValueTripleByte(v: ScalarValue) -> Sequence<u8> {
                    let mut x: u8 = (v & 63 as u32) as u8;
                    let mut y: u8 = ((v & 4032 as u32) >> truncate!(int!(6), u8)) as u8;
                    let mut z: u8 = ((v & 61440 as u32) >> truncate!(int!(12), u8)) as u8;
                    let mut firstByte: u8 = 224 as u8 | z;
                    let mut secondByte: u8 = 128 as u8 | y;
                    let mut thirdByte: u8 = 128 as u8 | x;
                    seq![firstByte, secondByte, thirdByte]
                }
                /// DafnyStandardLibraries-rs.dfy(13793,3)
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
                /// DafnyStandardLibraries-rs.dfy(13811,3)
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
                /// DafnyStandardLibraries-rs.dfy(13823,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstByte: u8 = m.get(&int!(0));
                    let mut x: u8 = firstByte;
                    x as u32
                }
                /// DafnyStandardLibraries-rs.dfy(13833,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstByte: u8 = m.get(&int!(0));
                    let mut secondByte: u8 = m.get(&int!(1));
                    let mut y: u32 = (firstByte & 31 as u8) as u32;
                    let mut x: u32 = (secondByte & 63 as u8) as u32;
                    y << truncate!(int!(6), u8) | x
                }
                /// DafnyStandardLibraries-rs.dfy(13845,3)
                pub fn DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq) -> ScalarValue {
                    let mut firstByte: u8 = m.get(&int!(0));
                    let mut secondByte: u8 = m.get(&int!(1));
                    let mut thirdByte: u8 = m.get(&int!(2));
                    let mut z: u32 = (firstByte & 15 as u8) as u32;
                    let mut y: u32 = (secondByte & 63 as u8) as u32;
                    let mut x: u32 = (thirdByte & 63 as u8) as u32;
                    z << truncate!(int!(12), u8) | y << truncate!(int!(6), u8) | x
                }
                /// DafnyStandardLibraries-rs.dfy(13860,3)
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
                /// DafnyStandardLibraries-rs.dfy(13268,3)
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
                /// DafnyStandardLibraries-rs.dfy(13294,3)
                pub fn PartitionCodeUnitSequence(s: &crate::Std::Unicode::Utf8EncodingForm::WellFormedCodeUnitSeq) -> Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq> {
                    crate::Std::Unicode::Utf8EncodingForm::_default::PartitionCodeUnitSequenceChecked(s).Extract()
                }
                /// DafnyStandardLibraries-rs.dfy(13322,3)
                pub fn IsWellFormedCodeUnitSequence(s: &Sequence<u8>) -> bool {
                    matches!((&crate::Std::Unicode::Utf8EncodingForm::_default::PartitionCodeUnitSequenceChecked(s)).as_ref(), Success{ .. })
                }
                /// DafnyStandardLibraries-rs.dfy(13363,3)
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
                /// DafnyStandardLibraries-rs.dfy(13382,3)
                pub fn DecodeCodeUnitSequence(s: &crate::Std::Unicode::Utf8EncodingForm::WellFormedCodeUnitSeq) -> Sequence<ScalarValue> {
                    let mut parts: Sequence<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq> = crate::Std::Unicode::Utf8EncodingForm::_default::PartitionCodeUnitSequence(s);
                    let mut vs: Sequence<ScalarValue> = crate::Std::Collections::Seq::_default::MapPartialFunction::<crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq, ScalarValue>(&(Rc::new(move |x0: &crate::Std::Unicode::Utf8EncodingForm::MinimalWellFormedCodeUnitSeq| crate::Std::Unicode::Utf8EncodingForm::_default::DecodeMinimalWellFormedCodeUnitSubsequence(x0)) as Rc<dyn ::std::ops::Fn(&_) -> _>), &parts);
                    vs.clone()
                }
                /// DafnyStandardLibraries-rs.dfy(13399,3)
                pub fn DecodeErrorMessage(index: &DafnyInt) -> Sequence<DafnyChar> {
                    string_of("Could not decode byte at index ").concat(&crate::Std::Strings::_default::OfInt(index))
                }
                /// DafnyStandardLibraries-rs.dfy(13404,3)
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

            /// DafnyStandardLibraries-rs.dfy(13445,3)
            pub type WellFormedCodeUnitSeq = Sequence<u8>;

            /// An element of WellFormedCodeUnitSeq
            pub fn __init_WellFormedCodeUnitSeq() -> Sequence<u8> {
                seq![] as Sequence<u8>
            }

            /// DafnyStandardLibraries-rs.dfy(13449,3)
            pub type MinimalWellFormedCodeUnitSeq = Sequence<u8>;
        }

        /// DafnyStandardLibraries-rs.dfy(13886,1)
        pub mod Utf8EncodingScheme {
            pub use ::dafny_runtime::Sequence;
            pub use ::std::rc::Rc;

            pub struct _default {}

            impl _default {
                /// DafnyStandardLibraries-rs.dfy(13887,3)
                pub fn Serialize(s: &Sequence<u8>) -> Sequence<u8> {
                    crate::Std::Collections::Seq::_default::Map::<u8, u8>(&({
                            Rc::new(move |c: &u8| -> u8{
            c.clone() as u8
        }) as Rc<dyn ::std::ops::Fn(&_) -> _>
                        }), s)
                }
                /// DafnyStandardLibraries-rs.dfy(13892,3)
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

    /// DafnyStandardLibraries-rs.dfy(13935,1)
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
            /// DafnyStandardLibraries-rs.dfy(13936,3)
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

        /// DafnyStandardLibraries-rs.dfy(13944,3)
        #[derive(Clone)]
        pub enum Option<T: DafnyType> {
            None {},
            Some {
                value: T
            }
        }

        impl<T: DafnyType> Option<T> {
            /// DafnyStandardLibraries-rs.dfy(13945,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), None{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(13950,5)
            pub fn PropagateFailure<_U: DafnyType>(&self) -> Rc<crate::Std::Wrappers::Option<_U>> {
                Rc::new(crate::Std::Wrappers::Option::None::<_U> {})
            }
            /// DafnyStandardLibraries-rs.dfy(13956,5)
            pub fn Extract(&self) -> T {
                self.value().clone()
            }
            /// DafnyStandardLibraries-rs.dfy(13962,5)
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
            /// DafnyStandardLibraries-rs.dfy(13971,5)
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
            /// DafnyStandardLibraries-rs.dfy(13980,5)
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
            /// DafnyStandardLibraries-rs.dfy(13989,5)
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

        /// DafnyStandardLibraries-rs.dfy(13995,3)
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
            /// DafnyStandardLibraries-rs.dfy(13996,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), Failure{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(14001,5)
            pub fn PropagateFailure<_U: DafnyType>(&self) -> Rc<crate::Std::Wrappers::Result<_U, E>> {
                Rc::new(crate::Std::Wrappers::Result::Failure::<_U, E> {
                        error: self.error().clone()
                    })
            }
            /// DafnyStandardLibraries-rs.dfy(14007,5)
            pub fn Extract(&self) -> R {
                self.value().clone()
            }
            /// DafnyStandardLibraries-rs.dfy(14013,5)
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
            /// DafnyStandardLibraries-rs.dfy(14022,5)
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
            /// DafnyStandardLibraries-rs.dfy(14031,5)
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
            /// DafnyStandardLibraries-rs.dfy(14040,5)
            pub fn Map<_FC: DafnyType>(&self, rewrap: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Wrappers::Result<R, E>>) -> _FC>) -> _FC {
                rewrap(&Rc::new(self.clone()))
            }
            /// DafnyStandardLibraries-rs.dfy(14045,5)
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

        /// DafnyStandardLibraries-rs.dfy(14055,3)
        #[derive(Clone)]
        pub enum Outcome<E: DafnyType> {
            Pass {},
            Fail {
                error: E
            }
        }

        impl<E: DafnyType> Outcome<E> {
            /// DafnyStandardLibraries-rs.dfy(14056,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), Fail{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(14061,5)
            pub fn PropagateFailure(&self) -> Rc<crate::Std::Wrappers::Outcome<E>> {
                Rc::new(self.clone())
            }
            /// DafnyStandardLibraries-rs.dfy(14067,5)
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
            /// DafnyStandardLibraries-rs.dfy(14076,5)
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
            /// DafnyStandardLibraries-rs.dfy(14085,5)
            pub fn Map<_FC: DafnyType>(&self, rewrap: &Rc<dyn ::std::ops::Fn(&Rc<crate::Std::Wrappers::Outcome<E>>) -> _FC>) -> _FC {
                rewrap(&Rc::new(self.clone()))
            }
            /// DafnyStandardLibraries-rs.dfy(14090,5)
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
            /// DafnyStandardLibraries-rs.dfy(14099,5)
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

        /// DafnyStandardLibraries-rs.dfy(14108,3)
        #[derive(Clone)]
        pub enum OutcomeResult<E: DafnyType> {
            _Pass_k {},
            _Fail_k {
                error: E
            }
        }

        impl<E: DafnyType> OutcomeResult<E> {
            /// DafnyStandardLibraries-rs.dfy(14109,5)
            pub fn IsFailure(&self) -> bool {
                matches!((&Rc::new(self.clone())).as_ref(), _Fail_k{ .. })
            }
            /// DafnyStandardLibraries-rs.dfy(14114,5)
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
  crate::SimpleFileIO::_default::Main(&dafny_args);
}