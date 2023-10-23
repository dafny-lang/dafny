using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

interface IAmbiguousThing<Thing> {
  /// <summary>
  /// Returns a plural number of non-null Thing's
  /// </summary>
  ISet<Thing> Pool { get; }
}

class AmbiguousThingHelper<Thing> where Thing : class {
  public static Thing Create(ModuleDefinition m, Thing a, Thing b, IEqualityComparer<Thing> eq, out ISet<Thing> s) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(eq != null);
    Contract.Ensures(Contract.Result<Thing>() != null ||
                     Contract.ValueAtReturn(out s) != null || 2 <= Contract.ValueAtReturn(out s).Count);
    s = null;
    if (eq.Equals(a, b)) {
      return a;
    }

    ISet<Thing> sa = a is IAmbiguousThing<Thing> ? ((IAmbiguousThing<Thing>)a).Pool : new HashSet<Thing>()
    {
      a
    };
    ISet<Thing> sb = b is IAmbiguousThing<Thing> ? ((IAmbiguousThing<Thing>)b).Pool : new HashSet<Thing>()
    {
      b
    };
    var union = new HashSet<Thing>(sa.Union(sb, eq));
    if (sa.Count == union.Count) {
      // sb is a subset of sa
      return a;
    } else if (sb.Count == union.Count) {
      // sa is a subset of sb
      return b;
    } else {
      s = union;
      Contract.Assert(2 <= s.Count);
      return null;
    }
  }

  public static string Name(ISet<Thing> s, Func<Thing, string> name) {
    Contract.Requires(s != null);
    Contract.Requires(s.Count != 0);
    string nm = null;
    foreach (var thing in s) {
      string n = name(thing);
      if (nm == null) {
        nm = n;
      } else {
        nm += "/" + n;
      }
    }

    return nm;
  }

  public static string ModuleNames(IAmbiguousThing<Thing> amb, Func<Thing, string> moduleName) {
    Contract.Requires(amb != null);
    Contract.Ensures(Contract.Result<string>() != null);
    string nm = null;
    foreach (var d in amb.Pool) {
      if (nm == null) {
        nm = moduleName(d);
      } else {
        nm += ", " + moduleName(d);
      }
    }

    return nm;
  }
}