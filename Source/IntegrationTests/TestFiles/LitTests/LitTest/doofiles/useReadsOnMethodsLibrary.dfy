// RUN: %build -t:lib --reads-clauses-on-methods "%S/Inputs/readsOnMethodsLibrary.dfy" --output "%T/readsOnMethodsLibrary.doo" > "%t"
// RUN: %resolve %s --library "%T/readsOnMethodsLibrary.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

module Client {
  import Library

  method Bar() {
    Library.Foo();
  }
}