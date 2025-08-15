#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
#![cfg_attr(any(), rustfmt::skip)]

mod WorkingFileIOTest_externs;

pub mod _module {
    
}
/// *****************************************************************************
///  Copyright by the contributors to the Dafny Project
///  SPDX-License-Identifier: MIT
/// *****************************************************************************
/// Source/DafnyStandardLibraries/examples/WorkingFileIOTest.dfy(7,1)
pub mod WorkingFileIOTest {
    pub use ::dafny_runtime::Sequence;
    pub use ::dafny_runtime::DafnyChar;
    pub use ::dafny_runtime::string_of;
    pub use ::std::rc::Rc;
    pub use crate::WorkingFileIOTest::Result::Success;
    pub use ::dafny_runtime::DafnyPrintWrapper;
    pub use ::dafny_runtime::int;
    pub use ::dafny_runtime::DafnyType;
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
        pub fn ReadBytesFromFile(
            path: &Sequence<DafnyChar>,
        ) -> Rc<Result<Sequence<u8>, Sequence<DafnyChar>>> {
            crate::WorkingFileIOTest_externs::_default::ReadBytesFromFile(path)
        }

        /// Source/DafnyStandardLibraries/examples/WorkingFileIOTest.dfy(16,3)
        pub fn Main(_noArgsParameter: &Sequence<Sequence<DafnyChar>>) -> () {
            let mut filename: Sequence<DafnyChar> = string_of("Source/DafnyStandardLibraries/examples/WorkingFileIOTest.dfy");
            let mut readResult: Rc<Result<Sequence<u8>, Sequence<DafnyChar>>>;
            let mut _out0: Rc<Result<Sequence<u8>, Sequence<DafnyChar>>> = _default::ReadBytesFromFile(&filename);
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
                if int!(0) < content.cardinality() {
                    print!("{}", DafnyPrintWrapper(&string_of("FileIO Rust backend test: PASSED\n")))
                } else {
                    print!("{}", DafnyPrintWrapper(&string_of("FileIO Rust backend test: FAILED (empty file)\n")))
                }
            } else {
                let mut ___mcc_h1: Sequence<DafnyChar> = _source0.error().clone();
                let mut error: Sequence<DafnyChar> = ___mcc_h1.clone();
                print!("{}", DafnyPrintWrapper(&string_of("Failed to read file: ")));
                print!("{}", DafnyPrintWrapper(&error));
                print!("{}", DafnyPrintWrapper(&string_of("\n")));
                print!("{}", DafnyPrintWrapper(&string_of("FileIO Rust backend test: FAILED\n")))
            };
            return ();
        }
    }

    /// Source/DafnyStandardLibraries/examples/WorkingFileIOTest.dfy(10,3)
    #[derive(Clone)]
    pub enum Result<T: DafnyType, E: DafnyType> {
        Success {
            value: T
        },
        Failure {
            error: E
        }
    }

    impl<T: DafnyType, E: DafnyType> Result<T, E> {
        /// Gets the field value for all enum members which have it
        pub fn value(&self) -> &T {
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

    impl<T: DafnyType, E: DafnyType> Debug
        for Result<T, E> {
        fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
            DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T: DafnyType, E: DafnyType> DafnyPrint
        for Result<T, E> {
        fn fmt_print(&self, _formatter: &mut Formatter, _in_seq: bool) -> std::fmt::Result {
            match self {
                Result::Success{value, } => {
                    write!(_formatter, "WorkingFileIOTest.Result.Success(")?;
                    DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
                Result::Failure{error, } => {
                    write!(_formatter, "WorkingFileIOTest.Result.Failure(")?;
                    DafnyPrint::fmt_print(error, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
        }
    }

    impl<T: DafnyType + Eq + Hash, E: DafnyType + Eq + Hash> PartialEq
        for Result<T, E> {
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

    impl<T: DafnyType + Eq + Hash, E: DafnyType + Eq + Hash> Eq
        for Result<T, E> {}

    impl<T: DafnyType + Hash, E: DafnyType + Hash> Hash
        for Result<T, E> {
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

    impl<T: DafnyType, E: DafnyType> AsRef<Result<T, E>>
        for Result<T, E> {
        fn as_ref(&self) -> &Self {
            self
        }
    }
}
fn main() {
  let args: Vec<String> = ::std::env::args().collect();
  let dafny_args =
    ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(
    &args, |s| 
  ::dafny_runtime::dafny_runtime_conversions::unicode_chars_true::string_to_dafny_string(s));
  crate::WorkingFileIOTest::_default::Main(&dafny_args);
}