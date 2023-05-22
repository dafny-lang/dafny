// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate prop()
ensures prop; // OOPS! Forgot () after prop
{
true
}
