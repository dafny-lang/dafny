// NONUNIFORM: Test that the Rust generated code contains docstrings
// RUN: %baredafny build --target:rs --enforce-determinism "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%S/docstring-rust/src/docstring.rs" "%S/docstring.check"
// RUN: "%S/docstring-rust/cargo" test --doc

/** Docstring for test method
  * Multi-line
  * How to call in Dafny
  * ```
  * TestMethod("hello");
  * ```
  * How to call in Rust (this will be checked with cargo doc)
  * ```rs
  * use docstring::_module::_default as Doc;
  * Doc::TestMethod(&::dafny_runtime::dafny_runtime_conversions::unicode_chars_true::string_to_dafny_string(&"hello".to_string()));
  * ```
  * It
  *
  *  should
  *
  *   work
  *
  *    for any indentation
  *
  *     And this indented comment should not be compiled to Rust executable docstring
  *
  **/
method TestMethod(s: string) { }
/** Docstring for functions */
function TestFn(): SynonymType { 1 }
/** Docstring for classes 1 */
class TestClass {}
/** Docstring for datatype */
datatype TestDatatype =
  | Constructor1() // Docstring for Constructor1
  | Constructor2() // Docstring for Constructor2

/** Docstring for synonym type */ 
type SynonymType = x: int | true

/** Docstring for module */
module SubModule {
  /** Docstring for classes 2 */
  class TestClass {
    /** Docstring for const */
    const testConst: bool
    /** Docstring for class constructor */
    constructor() {
      testConst := true;
    }
    predicate SingleLineFunction() { true } // Docstring for predicate
  }
}