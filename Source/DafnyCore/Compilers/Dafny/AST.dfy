
module {:extern "DAST"} DAST {

	datatype Program = Program(content: string)

  class ASTBuilder {
		
	  static method CreateProgram() returns (o: Program) {
			o := Program("Hi\n");
		}

  }
		
}
