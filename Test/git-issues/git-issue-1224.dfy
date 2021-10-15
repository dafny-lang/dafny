// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module SlowPoke {
  lemma {:timeLimitMultiplier 4} SlowLemma()
}

module SlowChild refines SlowPoke { }
