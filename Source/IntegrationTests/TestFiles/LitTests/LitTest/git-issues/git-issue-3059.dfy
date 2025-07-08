// RUN: %exits-with 4 %verify --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type seq0 = s: seq<int> | forall n <- s :: n == 0

ghost function ReplaceInSeq0_Rejects(s: seq0): seq0
  requires |s| > 0
  ensures false
{
  var s' := s[0 := 1];
  assert s'[0] != 0;
  s' // error: s' does not satisfy subset-type constraint
}

ghost function ReplaceInSeq0_Accepts(s: seq0): seq<int>
  requires |s| > 0
{
  var s' := s[0 := 1];
  assert s'[0] != 0;
  s'
}

type map0 = m: map<int, int> | forall k <- m :: m[k] == 0

ghost function AddInMap0_Rejects(m: map0): map0
  ensures false
{
  m[0 := 1] // error: s' does not satisfy subset-type constraint
}

ghost function AddInMap0_Accepts(m: map0): map<int, int>
{
  m[0 := 1]
}

ghost function RecoverType<T>(a: T): T { a }

method AddInMap0_Proxy_Rejects() returns (r: map0)
  ensures false
{
  var m; // The type of m is to be inferred, but that won't happen until
         // after type inference has processed the assignment to r.
  r := m[1 := 7]; // error: s' does not satisfy subset-type constraint
  // To trigger the unsoundness, the verifier needs to be reminded that
  // r is a variable of type map0. That is done by the following little
  // trick:
  ghost var u := RecoverType<map0>(r);
}

method AddInMap0_Proxy_Accepts() returns (r: map<int, int>)
{
  var m; // The type of m is to be inferred, but that won't happen until
         // after type inference has processed the assignment to r.
  r := m[1 := 7];
  // To trigger the unsoundness, the verifier needs to be reminded that
  // r is a variable of type map0. That is done by the following little
  // trick:
  ghost var u := RecoverType<map<int, int>>(r);
}

type multiset2 = s: multiset<int> | forall n <- s :: s[n] == 2 // everything in the multiset has multiplicity 2

ghost function ReplaceInMultiset2_Rejects(s: multiset2): multiset2
  ensures false
{
  var s' := s[0 := 1];
  assert s'[0] != 2;
  s' // error: s' does not satisfy subset-type constraint
}

ghost function ReplaceInMultiset2_Accepts(s: multiset2): multiset<int>
{
  var s' := s[0 := 1];
  assert s'[0] != 0;
  s'
}
