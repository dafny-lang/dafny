include "../Dafny/AST.dfy"

module {:extern "DCOMP"} DCOMP {

  import opened DAST

  class COMP {
		
	  static method Compile(p: Program) returns (s: string) {
		  s := p.content;
		}

  }
		
}