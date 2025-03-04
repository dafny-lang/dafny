// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate prop()
  ensures prop // OOPS! Forgot () after prop
{
  true
}
