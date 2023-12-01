using System.Threading.Tasks;
using Microsoft.Dafny;

namespace Dafny;

public class Dafny {
  public static Task<int> Main(string[] args) {
    return DafnyCli.Main(args);
  }
}
