
module {:extern "DAST"} DAST {

	datatype Program = Program(string)

  class ASTBuilder {
		
	  static method CreateProgram() returns (o: Program) {
			o := Program("Hi\n");
		}

  }
		
}
