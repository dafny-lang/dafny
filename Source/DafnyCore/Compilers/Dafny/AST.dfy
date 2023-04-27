
module {:extern "DAST"} DAST {

  datatype Program = Program(content: string)

  class ASTBuilder {
		
	  static function CreateProgram(s: string) : Program {
			Program(s)
		}

  }
		
}
