include "Imp.dfy"
include "SemanticsCommon.dfy"
include "Semantics.dfy"	

// For now we depend on ImpNaturalSem.dfy for the semantics of expressions
// We should modularize the code more

include "ImpNaturalSem.dfy"

type configuration = (com,store)

least predicate red(conf1: configuration, conf2: configuration) {
	var (c1,s1) := conf1;
	var (c2,s2) := conf2;
	
	match (c1, c2) {
		case (CSeq(CSkip,c),_) => s1 == s2 && c2 == c 
		case (CAsgn(id,a), CSkip) => 
			if (forall id: ident :: id_in_aexp(id,a) ==> id in s1) then
			s2 == s1[id := aeval(s1,a)]
			else false

		case (CSeq(ci1,ci3),CSeq(ci2,ci4)) => ci3 == ci4 && red((ci1,s1),(ci2,s2))

		case (CIf(bi1,ci1,ci2),_) =>
			if (forall id: ident :: id_in_bexp(id,bi1) ==> id in s1) then
			if beval(s1,bi1) then c2 == ci1 else c2 == ci2
			else false

		case (CWhile(bi1,ci1),Cskip) =>
			if (forall id: ident :: id_in_bexp(id,bi1) ==> id in s1) then
			!beval(s1,bi1) && s1 == s2
			else false
				
		case (CWhile(bi1,ci1),CSeq(ci2,CWhile(bi2,ci3))) => 
			if (forall id: ident :: id_in_bexp(id,bi1) ==> id in s1) then
			beval(s1,bi1) && s1 == s2 && bi1 == bi2 && ci1 == ci2 == ci3
			else false
		
		case (_,_) => false

	}

}

predicate fin_reds(conf1: configuration, conf2: configuration) {
	star((c1,c2) => red(c1,c2),conf1,conf2)
}
	
predicate inf_reds(conf: configuration) {
	inf((c1,c2) => red(c1,c2),conf)
}

// datatype test =
//  | RedAssign(ident,aexp,store)
//  | RedSeqDone(com,store)
//  | RedSeqStep(com,com,store,com,store)

// datatype tests =
//  | Single(test)
//  | More(tests)

// codatatype itests =
// 	| Single(test,itests)
 
// least predicate test_def(e: test, conf1: configuration, conf2: configuration) {
// 	match e {
// 		case RedAssign(id,a,s) => conf1 == (CAsgn(id,a),s) && conf2 == (CSkip,s) 
// 		case RedSeqDone(c,s) => conf1 == (CSeq(CSkip,c),s) && conf2 == (c,s)
// 		case RedSeqStep(c1,c,s1,c2,s2) => test_def(e,(c1,s1),(c2,s2)) && conf1 == (CSeq(c1,c),s1) && conf2 == (CSeq(c1,c),s2) 
// 	}
// }
	
