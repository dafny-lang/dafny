// RUN: %exits-with 2 %baredafny translate cs %args %s --translation-record %S/NoGood.dtr &> %t
// RUN: %diff "%s.expect" "%t"

method Main() {

}