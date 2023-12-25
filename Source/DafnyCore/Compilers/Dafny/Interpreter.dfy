module {:extern "D2DInterpreter"} Interpreter {

  import DAST
  import UnsupportedFeature

  class Interpreter {

    static method Run(d: seq<DAST.Module>) {
      print("Hello, world!\n");
    }

  }

}