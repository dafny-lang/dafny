using Microsoft.Dafny;

namespace Dafny;

public class Dafny {
  public static int Main(string[] args) {
    ParserErrorDetail.init();
    return DafnyDriver.Main(args);
  }
}
