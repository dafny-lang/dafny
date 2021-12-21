using System;

namespace DafnyProfiling {
  public class CodeCoverage {
    static uint[] tallies;
    public static void Setup(int size) {
      tallies = new uint[size];
    }
    public static void TearDown() {
      for (var i = 0; i < tallies.Length; i++) {
        Console.WriteLine("{0}: {1}", i, tallies[i]);
      }
      tallies = null;
    }
    public static bool Record(int id) {
      tallies[id]++;
      return true;
    }
  }
}
