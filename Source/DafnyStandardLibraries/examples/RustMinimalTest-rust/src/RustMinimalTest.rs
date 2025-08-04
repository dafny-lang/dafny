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
fn main() {
  let args: Vec<String> = ::std::env::args().collect();
  let dafny_args =
    ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(
    &args, |s| 
  ::dafny_runtime::dafny_runtime_conversions::unicode_chars_true::string_to_dafny_string(s));
  crate::_module::_default::_Test__Main_(&dafny_args);
}