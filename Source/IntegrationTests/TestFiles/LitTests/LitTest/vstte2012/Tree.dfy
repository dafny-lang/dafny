// RUN: %testDafnyForEachResolver "%s"


// The tree datatype
datatype Tree = Leaf | Node(Tree, Tree)


// This datatype is used for the result of the build functions.
// These functions either fail or yield a tree. Since we use
// a side-effect free implementation of the helper
// build_rec, it also has to yield the rest of the sequence,
// which still needs to be processed. For function build,
// this part is not used.
datatype Result = Fail | Res(t: Tree, sOut: seq<int>)


// Function toList converts a tree to a sequence.
// We use Dafny's built-in value type sequence rather than
// an imperative implementation to simplify verification.
// The argument d is added to each element of the sequence;
// it is analogous to the argument d in build_rec.
// The postconditions state properties that are needed
// in the completeness proof.
ghost function toList(d: int, t: Tree): seq<int>
  ensures toList(d, t) != [] && toList(d, t)[0] >= d
  ensures (toList(d, t)[0] == d) == (t == Leaf)
  decreases t
{
  match t
  case Leaf => [d]
  case Node(l, r) => toList(d+1, l) + toList(d+1, r)
}


// Function build_rec is a side-effect free implementation
// of the code given in the problem statement.
// The first postcondition is needed to show that the
// termination measure indeed decreases.
// The second postcondition specifies the soundness
// property; converting the resulting tree back into a
// sequence yields exactly that portion of the input
// sequence that has been consumed.
function {:isolate_assertions} build_rec(d: int, s: seq<int>): Result
  ensures build_rec(d, s).Res? ==>
            |build_rec(d, s).sOut| < |s| &&
            build_rec(d, s).sOut == s[|s|-|build_rec(d, s).sOut|..]
  ensures build_rec(d, s).Res? ==>
            toList(d,build_rec(d, s).t) == s[..|s|-|build_rec(d, s).sOut|]
  decreases |s|, (if s==[] then 0 else s[0]-d)
{
  if s==[] || s[0] < d then
    Fail
  else if s[0] == d then
    Res(Leaf, s[1..])
  else
    var left := build_rec(d+1, s);
    if left.Fail? then Fail else
    var right := build_rec(d+1, left.sOut);
    if right.Fail? then Fail else
    Res(Node(left.t, right.t), right.sOut)
}


// Function build is a side-effect free implementation
// of the code given in the problem statement.
// The postcondition specifies the soundness property;
// converting the resulting tree back into a
// sequence yields exactly the input sequence.
// Completeness is proved as a lemma, see below.
function build(s: seq<int>): Result
  ensures build(s).Res? ==> toList(0,build(s).t) == s
{
  var r := build_rec(0, s);
  if r.Res? && r.sOut == [] then r else Fail
}


// This is the main lemma for the
// completeness theorem. If a sequence s starts with a
// valid encoding of a tree t then build_rec yields a
// result (i.e., does not fail) and the rest of the sequence.
// The body of the method proves the lemma by structural
// induction on t. Dafny proves termination (using the
// height of the term t as termination measure), which
// ensures that the induction hypothesis is applied
// correctly (encoded by calls to this lemma).
lemma lemma0(t: Tree, d: int, s: seq<int>)
  ensures build_rec(d, toList(d, t) + s).Res? &&
          build_rec(d, toList(d, t) + s).sOut == s
{
  match(t) {
  case Leaf =>
    assert toList(d, t) == [d];
  case Node(l, r) =>
    assert t > l;
    assert toList(d, t) + s == toList(d+1, l) + (toList(d+1, r) + s);
    // the rest follows from (two invocations of) the (automatically applied) induction hypothesis
  }
}


// This lemma states the
// completeness property. It is proved by applying the
// main lemma (lemma0). In this lemma, the bound variables
// of the completeness theorem are passed as arguments;
// the following two lemmas replace these arguments
// by quantified variables.
lemma lemma1(t: Tree, s:seq<int>)
  requires s == toList(0, t) + []
  ensures build(s).Res?
{
  lemma0(t, 0, []);
}


// This lemma introduces the existential quantifier in the completeness
// property.
lemma lemma2(s: seq<int>)
  ensures (exists t: Tree :: toList(0,t) == s) ==> build(s).Res?
{
  forall t | toList(0,t) == s {
    lemma1(t, s);
  }
}


// This lemma encodes the completeness theorem.
// For each sequence for which there is a corresponding
// tree, function build yields a result different from Fail.
// The body of the method converts the argument of lemma2
// into a universally quantified variable.
lemma completeness()
  ensures forall s: seq<int> :: ((exists t: Tree :: toList(0,t) == s) ==> build(s).Res?)
{
  forall s {
    lemma2(s);
  }
}


// This method encodes the first test harness
// given in the problem statement. The local
// assertions are required by the verifier to
// unfold the necessary definitions.
method harness0()
  ensures build([1,3,3,2]).Res? &&
          build([1,3,3,2]).t == Node(Leaf, Node(Node(Leaf, Leaf), Leaf))
{
}


// This method encodes the second test harness
// given in the problem statement. The local
// assertions are required by the verifier to
// unfold the necessary definitions.
method harness1()
  ensures build([1,3,2,2]).Fail?
{
}
