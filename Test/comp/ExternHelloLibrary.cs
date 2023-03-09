// Note that  ExternHelloLibrary.dll was produced from this file using
// csc /t:library ExternHelloLibrary.cs
using System;

namespace ExternHelloLibrary {
  public static class ExternHelloLibrary {
    public static void SayHello() {
      Console.WriteLine("Hello from ExternHelloLibrary.");
    }
  }
}
