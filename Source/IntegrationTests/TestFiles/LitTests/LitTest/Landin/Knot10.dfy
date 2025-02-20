// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


datatype Pack<T> = Pack(ghost c: T)

method M()
  ensures false
{
  var r := new Pack<() ~> bool>[1];

  var tf := Pack(() reads r, r[0].c.reads => 
                     if r[0].c.requires() then !r[0].c() else false
                   );
  // the following would be trouble, if allowed, because then r[0] calls itself without decreasing
  r[0] := tf; // error: not allowed to assign a Pack<() ~> bool> to a heap memory location
}

method R0(r: array<Pack<() ~> bool>>)
  requires r.Length != 0
  modifies r
{
  // The syntactic use of a "reads" clause in the following line causes the lambda expression to be typed
  // as "() ~> bool". The assignment thus incurs a proof obligation that the function value doesn't actually
  // read the heap (despite its static type). If the rest of the program let us get past the resolver, then
  // the verifier can dismiss this proof obligation.
  // (The "Pack(...)" in the RHS may be typed as either "Pack(~>)" or "Pack(->)", but in either case, the
  // proof obligation just mentioned still applies, either directly to the lambda expression or to the entire
  // RHS.)
  var p: Pack<() -> bool> := Pack(() reads {} => false);
  // The types of the LHS ("Pack(~>)") and RHS ("Pack(->)") are allowed in the assignment, but they cause
  // a proof obligation that the RHS really is a "Pack(~>)". This verifier is able to prove that.
  // Therefore, there is neither a "~> assigned to memory" nor a "RHS not assignable to LHS" error in the
  // following line.
  r[0] := p;
  // Note, what was just said here about proof obligations and the verifier is confirmed in Knot18.dfy.
}

method R1(r: array<Pack<() ~> bool>>)
  requires r.Length != 0
  modifies r
{
  // The lambda expression in the following line is typed as "() -> bool", but the enclosing "Pack(...)"
  // is typed as "Pack<() ~> bool>" to match the LHS. However, an -> arrow is assignable to a ~>, so
  // the use of a "() -> bool" as the argument to the "Pack" constructor works just fine.
  var p: Pack<() ~> bool> := Pack(() => false);
  r[0] := p; // error: not allowed to assign a Pack<() ~> bool> to a heap memory location
}

method R2(r: array<Pack<() ~> bool>>)
  requires r.Length != 0
  modifies r
{
  // In the following line, the new resolver infers
  //   - the type of "() => false" to be "() -> bool", that is, an arrow without read effects
  //   - the type of the RHS to be "Pack<() -> bool>"
  // Since the LHS has type "Pack<() ~> bool>", the is a proof obligation that the RHS really is a "Pack<() ~> bool>".
  // As can be observed in R0, that proof obligation goes through.
  // In the legacy resolver, the RHS is typed liked the LHS, so the type of the RHS is "Pack<() ~> bool>". This means
  // that the check for assigning a ~> into a memory location fails.
  r[0] := Pack(() => false); // (legacy resolver) error: not allowed to assign a Pack<() ~> bool> to a heap memory location
}

method R3(r: array<Pack<() ~> bool>>)
  requires r.Length != 0
  modifies r
{
  // In the following line, the new resolver infers
  //   - the type of "() reads {} => false" to be "() ~> bool", that is, an arrow with potential read effects
  //   - the type of the RHS to be "Pack(() ~> bool)"
  // Due to the latter, the error we get is that a "~>" arrow is being assigned to a memory location.
  r[0] := Pack(() reads {} => false); // error: not allowed to assign a Pack<() ~> bool> to a heap memory location
}
