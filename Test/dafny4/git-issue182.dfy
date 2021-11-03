// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

compiled predicate prop()
ensures prop; // OOPS! Forgot () after prop
{
true
}
