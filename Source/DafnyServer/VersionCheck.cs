using System;

namespace DafnyServer {
  public class VersionCheck {
    private static readonly string _currentVersion = "1.9.16";

    public static void CurrentVersion() {
      Console.WriteLine("VERSION:" + _currentVersion);
    }
  }
}
