// RUN: %exits-with 3 %baredafny translate cs %args %s --translation-record %S/NoGood.dtr &> %t
// RUN: %exits-with 3 %baredafny translate cs %args %s --translation-record %S/WrongDafnyVersion.dtr &>> %t
// RUN: %diff "%s.expect" "%t"

method Main() {

}