include "../Dafny/AST.dfy"

module {:extern "FDafnyPlugin"} FDafnyPlugin {
  import opened DAST
  import PrettyPrinter

  class COMP {

    static method Compile(p: seq<Module>) returns (s: string) {
      s := PrettyPrinter.PrettyPrint(p);
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "Emit Main";
    }
  }
}
