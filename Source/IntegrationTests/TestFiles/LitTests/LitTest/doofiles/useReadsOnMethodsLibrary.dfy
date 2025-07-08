// RUN: %build -t:lib --reads-clauses-on-methods "%S/Inputs/readsOnMethodsLibrary.dfy" --output "%S/Output/readsOnMethodsLibrary.doo" > "%t"
// RUN: %resolve %s --library "%S/Output/readsOnMethodsLibrary.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

module Client {
  import Library

  method Bar() {
    Library.Foo();
  }
}