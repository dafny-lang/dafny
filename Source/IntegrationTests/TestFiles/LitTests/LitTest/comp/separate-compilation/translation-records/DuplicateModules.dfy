// RUN: %baredafny translate cs %args %S/Inputs/Foo.dfy &> %t
// RUN: %baredafny translate cs %args %S/Inputs/Bar.dfy &>> %t

// Valid
// RUN: %baredafny translate cs %args %S/Inputs/Foo.dfy --translation-record %S/Inputs/Bar-cs.dtr &>> %t

// Invalid: Foo can't be previously translated and to translate now
// RUN: %exits-with 3 %baredafny translate cs %args %S/Inputs/Foo.dfy --translation-record %S/Inputs/Foo-cs.dtr &>> %t

// Invalid: Bar can't appear in more than one translation record at the same time
// RUN: %exits-with 3 %baredafny translate cs %args %S/Inputs/Foo.dfy --translation-record %S/Inputs/Bar-cs.dtr --translation-record %S/Inputs/Bar-cs.dtr &>> %t

// RUN: %diff "%s.expect" "%t"
