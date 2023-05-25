// RUN: %exits-with 2 %baredafny verify %args --library:"%s" --verify-scope=Everything "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype FailureRestrictedType<T, R> = Failure

method m() returns (r: FailureRestrictedType<bool, bool>) {
    :- Failure;
    r := Failure;
}
