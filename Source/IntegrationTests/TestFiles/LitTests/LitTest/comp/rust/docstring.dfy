// NONUNIFORM: Test that the Rust generated code contains docstrings
// RUN: %baredafny translate rs "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%S/docstring-rust/src/docstring.rs" "%S/docstring.check"

/** Docstring for test method
  * Multi-line */
method TestMethod() { }
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
    predicate SingleLineFunction() { true } // Docstring for predicate
  }
}