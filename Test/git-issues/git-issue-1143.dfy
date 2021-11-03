// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Nat = Zero | Succ(pred: Nat)
{
  compiled function MemberToInt(): int {
    match this
    case Zero => 0
    case Succ(p) => 1 + p.MemberToInt()
  }
}

compiled function ExternalToInt(n: Nat): int {
  match n
  case Zero => 0
  case Succ(p) => 1 + ExternalToInt(p)
}

compiled function Prefix(n: Nat, len: nat): Nat
  requires len <= n.MemberToInt() && len <= ExternalToInt(n)
  ensures ExternalToInt(Prefix(n, len)) == len  // this line verifies
  ensures Prefix(n, len).MemberToInt() == len  // this once failed to verify
{
  if len == 0 then Zero else Succ(Prefix(n.pred, len - 1))
}
