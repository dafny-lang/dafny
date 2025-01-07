module {:extern "ResolvedDesugaredExecutableDafnyPlugin"} ResolvedDesugaredExecutableDafnyPlugin {
  import opened DAST
  import PrettyPrinter
  import UnsupportedFeature

  class COMP {

    static method Compile(p: seq<Module>) returns (s: string) {
      s := PrettyPrinter.PrettyPrint(p);
    }

    static method EmitCallToMain(fullName: Expression) returns (s: string) {
      s := "";
    }
  }
}
