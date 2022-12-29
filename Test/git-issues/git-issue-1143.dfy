// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Nat = Zero | Succ(pred: Nat)
{
  function method MemberToInt(): int {
    match this
    case Zero => 0
    case Succ(p) => 1 + p.MemberToInt()
  }
}

function method ExternalToInt(n: Nat): int {
  match n
  case Zero => 0
  case Succ(p) => 1 + ExternalToInt(p)
}

function method Prefix(n: Nat, len: nat): Nat
  requires len <= n.MemberToInt() && len <= ExternalToInt(n)
  ensures ExternalToInt(Prefix(n, len)) == len  // this line verifies
  ensures Prefix(n, len).MemberToInt() == len  // this once failed to verify
{
  if len == 0 then Zero else Succ(Prefix(n.pred, len - 1))
}
