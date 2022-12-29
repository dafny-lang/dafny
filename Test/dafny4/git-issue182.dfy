// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method prop()
ensures prop; // OOPS! Forgot () after prop
{
true
}
