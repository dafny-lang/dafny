// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Nat = Nat(n: nat)

datatype SeqNat = Seq(seqn: seq<Nat>) {
  predicate LessThan(n: nat) 
  decreases seqn
  {
    if seqn == [] then true else seqn[0].n < n && Seq(seqn[1..]).LessThan(n)
  }
}

predicate LessThan(ss: seq<SeqNat>, n: nat) {
  if ss == [] then true else
    ss[0].LessThan(n) && LessThan(ss[1..], n)
}

lemma Foo(ss: seq<SeqNat>, l: nat)
  requires l < |ss|
  requires LessThan(ss, 30)
  requires LessThan(ss, 239)
  ensures ss[l].LessThan(1) // error: (but this was once provable, due to a bug)
{
  if ss != [] {
    if l != 0 {
      Foo(ss[1..], l - 1);
      assert ss[1..][l - 1] == ss[l];
      assert ss[1..][l - 1..] == ss[l..];
    }
  }
}

method Main() {
  var sn: SeqNat := Seq([Nat(28)]);
  assert sn.LessThan(30);
  assert sn.LessThan(239);

  var ss := [sn];
  var l := 0;
  Foo(ss, l);

  // by the postcondition of Foo:
  assert ss[l].LessThan(1);
  assert ss[l] == sn;
  assert sn.LessThan(1);
  assert sn.seqn[0].n < 1;

  // yet:
  assert sn.seqn[0] == Nat(28);
  assert sn.seqn[0].n == 28;
  assert 28 < 1;
  assert false;

  print 10 / 0;
}
