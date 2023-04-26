
module {:extern "DafnyToDafny.AST"} AST {

	datatype Program = Program(string)

  class ASTBuilder {
		
	  static method CreateProgram(msg: string) returns (o: Program) {
			o := Program(msg);
		}

  }
		
}
