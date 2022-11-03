// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


Alas, the program causes Dafny to generate malformed Boogie code, because of the trigger Dafny generates for the quantifier.
