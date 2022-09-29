include "Mach.dfy"

predicate code_at(C: code, pc: nat, C2: code) {
	exists C1, C3: code :: C == C1 + C2 + C3 && |C1| == pc
}

lemma code_at_app_left(C: code, pc: nat, C1: code, C2: code)
	requires code_at(C,pc,C1 + C2)
	ensures code_at(C,pc,C1)
{
	var C0, C3 :| C == C0 + (C1 + C2) + C3 && |C0| == pc;
	assert C == C0 + C1 + (C2 + C3) && |C0| == pc;
}

lemma code_at_app_right(C: code, pc: nat, C1: code, C2: code)
	requires code_at(C,pc,C1 + C2)
	ensures code_at(C,pc + |C1|,C2)
{
	var C0, C3 :| C == C0 + (C1 + C2) + C3 && |C0| == pc;
	assert C == (C0 + C1) + C2 + C3 && |C0 + C1| == pc + |C1|;
}

lemma resolve_code_at()
	ensures forall C: code :: forall pc: nat :: forall C1, C2: code :: code_at(C,pc,C1 + C2) ==> code_at(C,pc,C1)
	ensures forall C: code :: forall pc: nat :: forall C1, C2: code :: code_at(C,pc,C1 + C2) ==> code_at(C,pc + |C1|,C2)
{
	forall C, pc, C1, C2 ensures code_at(C,pc,C1 + C2) ==> code_at(C,pc,C1) {
		if code_at(C,pc,C1 + C2) {
			code_at_app_left(C,pc,C1,C2);
		}
	}
	// Surprisingly, in what follows, if we do not provide the type annotation on pc,
	// then Dafny fails to recognize that pc is a nat
	forall C, pc: nat, C1, C2 ensures code_at(C,pc,C1 + C2) ==> code_at(C,pc + |C1|,C2) {
		if code_at(C,pc,C1 + C2) {
			code_at_app_right(C,pc,C1,C2);
		}
	}
}
