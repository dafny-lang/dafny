include "Imp.dfy"
include "ImpSem2.dfy"
include "MC.dfy"
include "Compiler.dfy"
include "Proof_com.dfy"


lemma compile_program_correct_terminating(s: store, c: com, s': store)
	requires cexec(s,c,s')
	ensures machine_terminates(compile_program(c),s,s')
{
	var C := compile_program(c);
	var pc := |C|-1;
	assert pc < |C|;
	assert code_at(C,0,compile_com(c)) by {
		assert C == [] + compile_com(c) + [Ihalt];
	}
	compile_com_correct_terminating(s,c,s',C,0,[]);
	assert transitions(C,(0,[],s),(pc,[],s'));
	assert compile_program(c)[pc] == Ihalt;
	
}
	
