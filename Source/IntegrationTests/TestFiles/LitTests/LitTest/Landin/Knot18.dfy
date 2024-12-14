// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Pack<T> = Pack(ghost c: T)

method R0(r: array<Pack<() ~> bool>>)
  requires r.Length != 0
  modifies r
{
  // For a description, see method R0 in Knot10.dfy.
  var p: Pack<() -> bool> := Pack(() reads {} => false);
  r[0] := p;
}

method R2(r: array<Pack<() ~> bool>>)
  requires r.Length != 0
  modifies r
{
  // In the following line, the new resolver infers
  //   - the type of "() => false" to be "() -> bool", that is, an arrow without read effects
  //   - the type of the RHS to be "Pack<() -> bool>"
  // Since the LHS has type "Pack<() ~> bool>", the is a proof obligation that the RHS really is a "Pack<() ~> bool>".
  r[0] := Pack(() => false);
}
