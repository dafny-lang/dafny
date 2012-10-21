// Example taken from:
// Edsger W. Dijkstra: Heuristics for a Calculational Proof. Inf. Process. Lett. (IPL) 53(3):141-143 (1995)
// Transcribed into Dafny by Valentin Wüstholz and Nadia Polikarpova.


function f(n: nat) : nat

ghost method theorem(n: nat)
  requires forall m: nat :: f(f(m)) < f(m + 1);
  ensures f(n) == n;
{
  calc
  {
    f(n);
    { lemma_ping(n, n); lemma_pong(n); }
    n;
  }
}

// Aiming at n <= f(n), but strengthening it for induction
ghost method lemma_ping(j: nat, n: nat)
  requires forall m: nat :: f(f(m)) < f(m + 1); // (0)
  ensures j <= n ==> j <= f(n);
{
  // The case for j == 0 is trivial
  if (0 < j <= n) {
    calc {
      j <= n;
      { lemma_ping(j - 1, n - 1); }
      j - 1 <= f(n - 1);
      { lemma_ping(j - 1, f(n - 1)); }
      ==> j - 1 <= f(f(n - 1));
      // (0)
      j - 1 <= f(f(n - 1)) && f(f(n - 1)) < f(n);
      ==> j - 1 < f(n);
      j <= f(n);
    }
  }
}

// The other directorion: f(n) <= n
ghost method lemma_pong(n: nat)
  requires forall m: nat :: f(f(m)) < f(m + 1);  // (0)
  ensures f(n) <= n;
{
  calc {
    true;
    // (0) with m := n
    f(f(n)) < f(n + 1);
    { lemma_monotonicity_0(n + 1, f(n)); }
    f(n) < n + 1;
    f(n) <= n;
  }
}

ghost method lemma_monotonicity_0(a: nat, b: nat)
  requires forall m: nat :: f(f(m)) < f(m + 1);
  ensures a <= b ==> f(a) <= f(b);  // or, equivalently:  f(b) < f(a) ==> b < a
  decreases b - a;
{
  // The case for a == b is trivial
  if (a < b) {
    calc <= {
      f(a);
      { lemma_monotonicity_1(a); }
      f(a + 1);
      { lemma_monotonicity_0(a + 1, b); }
      f(b);
    }
  }
}

ghost method lemma_monotonicity_1(n: nat)
  requires forall m: nat :: f(f(m)) < f(m + 1);  // (0)
  ensures f(n) <= f(n + 1);
{
  calc <= {
    f(n);
    { lemma_ping(f(n), f(n)); }
    f(f(n));
    // (0)
    f(n + 1);
  }
}
