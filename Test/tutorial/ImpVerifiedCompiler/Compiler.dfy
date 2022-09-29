include "Imp.dfy"
include "Mach.dfy"

function method compile_aexp(a: aexp): code {
	match a {
		case AConst(n) => [Iconst(n)]
		case AId(id) => [Ivar(id)]
		case APlus(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Iadd]
		case AMinus(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Iopp,Iadd]
	}
}

function method negb(b: bool): bool {
	if b then false else true
}

function method compile_bexp(b: bexp, d1: int, d0: int): code {
  match b {
		case BTrue => if d1 == 0 then [] else [Ibranch(d1)]
		case BFalse => if d0 == 0 then [] else [Ibranch(d0)]
		case BEq(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Ibeq(d1,d0)]   
		case BLe(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Ible(d1,d0)]
		case BNot(b1) => compile_bexp(b1, d0, d1)
		case BAnd(b1, b2) =>
      var c2 := compile_bexp(b2, d1, d0);
      var c1 := compile_bexp(b1, 0, |c2| + d0);
      c1 + c2
	}
}

function method compile_com(c: com): code {
	match c {
		case CSkip => []
		case CAsgn(id, a) => compile_aexp(a) + [Isetvar(id)]
		case CSeq(c1, c2) => compile_com(c1) + compile_com(c2)
		case CIf(b, ifso, ifnot) =>
			var code_ifso := compile_com(ifso);
			var code_ifnot := compile_com(ifnot);
			compile_bexp(b,0,|code_ifso| + 1)
			+ code_ifso + [Ibranch(|code_ifnot|)] + code_ifnot
		case CWhile(b, body) =>
			var code_body := compile_com(body);
			var code_test := compile_bexp(b,0,|code_body|+1);
			code_test + code_body + [Ibranch(-( |code_test| + |code_body| + 1))]
	}
}

function method compile_program(p: com): code {
	compile_com(p) + [Ihalt]
}


