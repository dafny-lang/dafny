#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
#![cfg_attr(any(), rustfmt::skip)]

pub mod _module {
    pub use ::dafny_runtime::Sequence;
    pub use ::dafny_runtime::DafnyChar;
    pub use ::dafny_runtime::string_of;
    pub use ::std::rc::Rc;
    pub use crate::Wrappers::Outcome;
    pub use crate::Wrappers::Outcome::Pass;
    pub use ::dafny_runtime::DafnyPrintWrapper;
    pub use crate::Wrappers::Result;
    pub use crate::Wrappers::Result::Success;

    pub struct _default {}

    impl _default {
        /// test_custom_fileio_rust.dfy(4,1)
        pub fn Main(_noArgsParameter: &Sequence<Sequence<DafnyChar>>) -> () {
            let mut testContent: Sequence<DafnyChar> = string_of("Hello, Rust FileIO!");
            let mut testPath: Sequence<DafnyChar> = string_of("test_file.txt");
            let mut writeResult: Rc<Outcome<Sequence<DafnyChar>>>;
            let mut _out0: Rc<Outcome<Sequence<DafnyChar>>> = crate::FileIO::_default::WriteUTF8ToFile(&testPath, &testContent);
            writeResult = _out0.clone();
            if matches!((&writeResult).as_ref(), Pass{ .. }) {
                print!("{}", DafnyPrintWrapper(&string_of("Successfully wrote to file\n")))
            } else {
                print!("{}", DafnyPrintWrapper(&string_of("Failed to write to file: ")));
                print!("{}", DafnyPrintWrapper(writeResult.error()));
                print!("{}", DafnyPrintWrapper(&string_of("\n")));
                return ();
            };
            let mut readResult: Rc<Result<Sequence<DafnyChar>, Sequence<DafnyChar>>>;
            let mut _out1: Rc<Result<Sequence<DafnyChar>, Sequence<DafnyChar>>> = crate::FileIO::_default::ReadUTF8FromFile(&testPath);
            readResult = _out1.clone();
            if matches!((&readResult).as_ref(), Success{ .. }) {
                print!("{}", DafnyPrintWrapper(&string_of("Successfully read from file: '")));
                print!("{}", DafnyPrintWrapper(readResult.value()));
                print!("{}", DafnyPrintWrapper(&string_of("'\n")))
            } else {
                print!("{}", DafnyPrintWrapper(&string_of("Failed to read from file: ")));
                print!("{}", DafnyPrintWrapper(readResult.error()));
                print!("{}", DafnyPrintWrapper(&string_of("\n")))
            };
            return ();
        }
    }
}
/// custom_fileio_rust.dfy(19,1)
pub mod FileIO {
    pub use ::dafny_runtime::Sequence;
    pub use ::dafny_runtime::DafnyChar;
    pub use ::std::rc::Rc;
    pub use crate::Wrappers::Result;
    pub use ::dafny_runtime::MaybePlacebo;
    pub use ::dafny_runtime::string_of;
    pub use ::dafny_runtime::DafnyInt;
    pub use ::dafny_runtime::integer_range;
    pub use ::dafny_runtime::int;
    pub use ::dafny_runtime::seq;
    pub use crate::Wrappers::Outcome;

    pub struct _default {}

    impl _default {
        /// custom_fileio_rust.dfy(24,3)
        pub fn ReadUTF8FromFile(path: &Sequence<DafnyChar>) -> Rc<Result<Sequence<DafnyChar>, Sequence<DafnyChar>>> {
            let mut result = MaybePlacebo::<Rc<Result<Sequence<DafnyChar>, Sequence<DafnyChar>>>>::new();
            let mut isError: bool;
            let mut bytesRead: Sequence<u8>;
            let mut errorMsg: Sequence<DafnyChar>;
            let mut _out0: bool;
            let mut _out1: Sequence<u8>;
            let mut _out2: Sequence<DafnyChar>;
            let _x = crate::_FileIOInternalExterns_Impl::_default::INTERNAL_ReadBytesFromFile(path);
            _out0 = _x.0;
            _out1 = _x.1;
            _out2 = _x.2;
            isError = _out0;
            bytesRead = _out1.clone();
            errorMsg = _out2.clone();
            if isError {
                result = MaybePlacebo::from(Rc::new(Result::Failure::<Sequence<DafnyChar>, Sequence<DafnyChar>> {
                                error: errorMsg.clone()
                            }));
                return result.read();
            };
            let mut text: Sequence<DafnyChar> = string_of("");
            let mut _hi0: DafnyInt = bytesRead.cardinality();
            for i in integer_range(int!(0), _hi0.clone()) {
                text = text.concat(&seq![DafnyChar(bytesRead.get(&i) as char)]);
            }
            result = MaybePlacebo::from(Rc::new(Result::Success::<Sequence<DafnyChar>, Sequence<DafnyChar>> {
                            value: text.clone()
                        }));
            return result.read();
        }
        /// custom_fileio_rust.dfy(41,3)
        pub fn WriteUTF8ToFile(path: &Sequence<DafnyChar>, content: &Sequence<DafnyChar>) -> Rc<Outcome<Sequence<DafnyChar>>> {
            let mut result = MaybePlacebo::<Rc<Outcome<Sequence<DafnyChar>>>>::new();
            let mut bytes: Sequence<u8> = seq![] as Sequence<u8>;
            let mut _hi0: DafnyInt = content.cardinality();
            for i in integer_range(int!(0), _hi0.clone()) {
                bytes = bytes.concat(&seq![content.get(&i).0 as u8]);
            }
            let mut isError: bool;
            let mut errorMsg: Sequence<DafnyChar>;
            let mut _out0: bool;
            let mut _out1: Sequence<DafnyChar>;
            let _x = crate::_FileIOInternalExterns_Impl::_default::INTERNAL_WriteBytesToFile(path, &bytes);
            _out0 = _x.0;
            _out1 = _x.1;
            isError = _out0;
            errorMsg = _out1.clone();
            if isError {
                result = MaybePlacebo::from(Rc::new(Outcome::Failure::<Sequence<DafnyChar>> {
                                error: errorMsg.clone()
                            }));
                return result.read();
            };
            result = MaybePlacebo::from(Rc::new(Outcome::Pass::<Sequence<DafnyChar>> {}));
            return result.read();
        }
        /// custom_fileio_rust.dfy(58,3)
        pub fn ReadBytesFromFile(path: &Sequence<DafnyChar>) -> Rc<Result<Sequence<u8>, Sequence<DafnyChar>>> {
            let mut result = MaybePlacebo::<Rc<Result<Sequence<u8>, Sequence<DafnyChar>>>>::new();
            let mut isError: bool;
            let mut bytesRead: Sequence<u8>;
            let mut errorMsg: Sequence<DafnyChar>;
            let mut _out0: bool;
            let mut _out1: Sequence<u8>;
            let mut _out2: Sequence<DafnyChar>;
            let _x = crate::_FileIOInternalExterns_Impl::_default::INTERNAL_ReadBytesFromFile(path);
            _out0 = _x.0;
            _out1 = _x.1;
            _out2 = _x.2;
            isError = _out0;
            bytesRead = _out1.clone();
            errorMsg = _out2.clone();
            if isError {
                result = MaybePlacebo::from(Rc::new(Result::Failure::<Sequence<u8>, Sequence<DafnyChar>> {
                                error: errorMsg.clone()
                            }));
                return result.read();
            };
            result = MaybePlacebo::from(Rc::new(Result::Success::<Sequence<u8>, Sequence<DafnyChar>> {
                            value: bytesRead.clone()
                        }));
            return result.read();
        }
        /// custom_fileio_rust.dfy(69,3)
        pub fn WriteBytesToFile(path: &Sequence<DafnyChar>, bytes: &Sequence<u8>) -> Rc<Result<(), Sequence<DafnyChar>>> {
            let mut result = MaybePlacebo::<Rc<Result<(), Sequence<DafnyChar>>>>::new();
            let mut isError: bool;
            let mut errorMsg: Sequence<DafnyChar>;
            let mut _out0: bool;
            let mut _out1: Sequence<DafnyChar>;
            let _x = crate::_FileIOInternalExterns_Impl::_default::INTERNAL_WriteBytesToFile(path, bytes);
            _out0 = _x.0;
            _out1 = _x.1;
            isError = _out0;
            errorMsg = _out1.clone();
            if isError {
                result = MaybePlacebo::from(Rc::new(Result::Failure::<(), Sequence<DafnyChar>> {
                                error: errorMsg.clone()
                            }));
                return result.read();
            };
            result = MaybePlacebo::from(Rc::new(Result::Success::<(), Sequence<DafnyChar>> {
                            value: ()
                        }));
            return result.read();
        }
    }
}
/// custom_fileio_rust.dfy(11,1)
pub mod _FileIOInternalExterns_Impl {
    pub use crate::_dafny_externs::FileIOInternalExterns_Impl::*;
}
/// custom_fileio_rust.dfy(3,1)
pub mod Wrappers {
    pub use ::dafny_runtime::DafnyType;
    pub use ::std::fmt::Debug;
    pub use ::std::fmt::Formatter;
    pub use ::dafny_runtime::DafnyPrint;
    pub use ::std::cmp::Eq;
    pub use ::std::hash::Hash;
    pub use ::std::cmp::PartialEq;
    pub use ::std::hash::Hasher;
    pub use ::std::convert::AsRef;

    /// custom_fileio_rust.dfy(5,3)
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
                    write!(_formatter, "Wrappers.Result.Success(")?;
                    DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
                Result::Failure{error, } => {
                    write!(_formatter, "Wrappers.Result.Failure(")?;
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

    /// custom_fileio_rust.dfy(8,3)
    #[derive(Clone)]
    pub enum Outcome<E: DafnyType> {
        Pass {},
        Failure {
            error: E
        }
    }

    impl<E: DafnyType> Outcome<E> {
        /// Gets the field error for all enum members which have it
        pub fn error(&self) -> &E {
            match self {
                Outcome::Pass{} => panic!("field does not exist on this variant"),
                Outcome::Failure{error, } => error,
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
                    write!(_formatter, "Wrappers.Outcome.Pass")?;
                    Ok(())
                },
                Outcome::Failure{error, } => {
                    write!(_formatter, "Wrappers.Outcome.Failure(")?;
                    DafnyPrint::fmt_print(error, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                },
            }
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
                (Outcome::Failure{error, }, Outcome::Failure{error: _2_error, }) => {
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
                Outcome::Failure{error, } => {
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
}
fn main() {
  let args: Vec<String> = ::std::env::args().collect();
  let dafny_args =
    ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(
    &args, |s| 
  ::dafny_runtime::dafny_runtime_conversions::unicode_chars_true::string_to_dafny_string(s));
  crate::_module::_default::Main(&dafny_args);
}