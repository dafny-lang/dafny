// RUN: %exits-with 4 %baredafny verify %args "%s" --rprint="%t.rprint" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = None | Some(get: T)

method CheckThatMessageIsVerifiedAssumingExpectFails(x: Option<string>) {
    expect x.None?, x.get;
    expect x.Some?, x.get; // error: destructor 'get' can only be applied to datatype values constructed by 'Some'
}
