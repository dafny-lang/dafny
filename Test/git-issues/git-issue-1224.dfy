// RUN: %testDafnyForEachResolver "%s"


abstract module SlowPoke {
  lemma {:timeLimitMultiplier 4} SlowLemma()
}

module SlowChild refines SlowPoke { }
