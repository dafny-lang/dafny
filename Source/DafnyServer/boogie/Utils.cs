using System;
using System.Collections.Generic;

namespace Microsoft.Boogie.ModelViewer.Dafny {
  
  public class Provider {
    public static Provider Instance = new();
    private Provider() { }

    public DafnyModel GetLanguageSpecificModel(Model m, ViewOptions opts)
    {
      var dm = new DafnyModel(m, opts);
      foreach (var s in m.States)
      {
        var sn = new DafnyModelState(dm, s);
        dm.states.Add(sn);
      }
      return dm;
    }
  }

  public static class Util {

    public static IEnumerable<T> Empty<T>() {
      yield break;
    }

    public static IEnumerable<T> Map<S, T>(this IEnumerable<S> inp,
      Func<S, T> conv) {
      foreach (var s in inp) yield return conv(s);
    }

  }
  
  public enum NameSeqSuffix {
    None,
    WhenNonZero,
    Always
  }

  public class ViewOptions {
    // 0 - Normal
    // 1 - Expert
    // 2 - Everything
    // 3 - Include the kitchen sink
    public int ViewLevel = 1;
    public bool DebugMode;
  }
}