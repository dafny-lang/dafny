include "../Dafny/AST.dfy"

module {:extern "DCOMPD"} DCOMP {
  import opened DAST

  class COMP {

    static method Compile(p: seq<Module>) returns (s: string) {
      print p;
      s := "Hello";
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "Emit Main";
    }
  }
}
