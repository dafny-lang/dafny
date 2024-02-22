module {:extern "D2DPrettyPrinter"} PrettyPrinter {

  import DAST
  import UnsupportedFeature

  method PrettyPrint(d: seq<DAST.Module>) returns (s: string) {
    UnsupportedFeature.Throw();
    s := "Not Implemented Yet";
  }

}
