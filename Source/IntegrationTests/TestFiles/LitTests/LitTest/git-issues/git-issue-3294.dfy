// RUN: %exits-with 2 %dafny /compile:0 /library:"%s" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype FailureRestrictedType<T, R> = Failure

method m() returns (r: FailureRestrictedType<bool, bool>) {
    :- Failure;
    r := Failure;
}
