// RUN: %build -t:lib --reads-on-methods "%S/Inputs/readsOnMethodsLibrary.dfy" --output "%T/readsOnMethodsLibrary.doo" > "%t"
// RUN: %resolve %s --library "%T/readsOnMethodsLibrary.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

import Library

method Bar() {
  Library.Foo();
}