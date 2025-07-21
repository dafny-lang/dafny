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
        /// simple_rust_test.dfy(1,1)
        pub fn Main(_noArgsParameter: &Sequence<Sequence<DafnyChar>>) -> () {
            print!("{}", DafnyPrintWrapper(&string_of("Hello World\n")));
            return ();
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