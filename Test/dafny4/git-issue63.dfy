// RUN: %dafny /compile:0 "%s" > "%t"
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
    reveal_ValidGlobalStateOpaque();
    gm[g][0]
}

ghost function GlobalUpdate(gm: globalsmap, g:string, v:int): globalsmap
    requires ValidGlobalStateOpaque(gm) && ValidGlobal(g)
    ensures ValidGlobalStateOpaque(GlobalUpdate(gm, g, v))
{
    reveal_ValidGlobalStateOpaque();
    gm[g := gm[g][0 := v]]
}

lemma test()
{
    ghost var gm1:globalsmap;
    ghost var g: string;
    ghost var v: int;
    assume ValidGlobal(g) && ValidGlobalStateOpaque(gm1);
		ghost var gm2 := GlobalUpdate(gm1, g, v);
    assert GlobalWord(gm2, g) == v;
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
    assert s0 == sp_update_reg(r, s1, s0);
}
