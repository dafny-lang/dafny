// RUN: %verify --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type globalsmap = map<string, seq<int>>

ghost predicate {:axiom} ValidGlobal(g:string)

ghost predicate {:opaque} ValidGlobalStateOpaque(globals: globalsmap)
{
    forall g :: ValidGlobal(g) <==> g in globals && |globals[g]| == 1
}

ghost function GlobalWord(gm:globalsmap, g:string): int
    requires ValidGlobalStateOpaque(gm) && ValidGlobal(g)
{
    reveal ValidGlobalStateOpaque();
    gm[g][0]
}

ghost function GlobalUpdate(gm: globalsmap, g:string, v:int): globalsmap
    requires ValidGlobalStateOpaque(gm) && ValidGlobal(g)
    ensures ValidGlobalStateOpaque(GlobalUpdate(gm, g, v))
{
    reveal ValidGlobalStateOpaque();
    gm[g := gm[g][0 := v]]
}

lemma test()
{
    ghost var gm1:globalsmap;
    ghost var g: string;
    ghost var v: int;
    assume ValidGlobal(g) && ValidGlobalStateOpaque(gm1);
	ghost var gm2 := GlobalUpdate(gm1, g, v);
    // Because ValidGlobal is not revealed in this scope,
    // it could simplify
    // gm[g := gm[g][0 := v]][g][0]
    // == gm[g][0 := v][0]
    // but it cannot simplify further because
    // it does not know that 0 < |gm[g]|, which is needed for simplification
    assert g in gm1 && |gm1[g]| == 1 ==>
      GlobalWord(gm2, g) == v;
}

datatype reg = R0|R1|R2|R3

ghost predicate {:opaque} ValidRegState(regs:map<reg, int>)
{
    forall r:reg :: r in regs
}

ghost function sp_update_reg(r:reg, sM:map<reg, int>, sK:map<reg, int>): map<reg, int>
    requires ValidRegState(sK) && ValidRegState(sM)
    ensures ValidRegState(sp_update_reg(r, sM, sK))
{
    reveal_ValidRegState();
    sK[r := sM[r]]
}

lemma test2() {
    var s0, s1;
    assume ValidRegState(s0) && ValidRegState(s1);
    assume s0 == s1;
    var r: reg;
    //reveal_ValidRegState();

    // Cannot simplify this because ValidRegState is not revealed in scope.
    assert r in s0 ==> s0 == sp_update_reg(r, s1, s0);
}
