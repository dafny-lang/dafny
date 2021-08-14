// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %dafny /compile:3 /trackPrintEffects:1 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// The errors in this file are produced regardless of /trackPrintEffects setting.

method {:print} M() {
}

ghost method {:print} N() { // error: cannot apply {:print} to ghost method
}

lemma {:print} L() { // error: cannot apply {:print} to lemma
}

function {:print} F(): int // error: cannot apply {:print} to function

function method {:print} G(): int // error: cannot apply {:print} to function

function {:print} H(): int { // error: cannot apply {:print} to function-by-method
  2
} by method {
  return 2;
}

twostate predicate {:print} P() { // error: cannot apply {:print} to function
  true
}

greatest predicate {:print} Q() { // error: cannot apply {:print} to function
  true
}

method {:print "badArgument"} O() { // error: {:print} does not allow an argument
}
