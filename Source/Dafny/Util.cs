using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Boogie;


namespace Microsoft.Dafny {
  class Util
  {
    public static string Comma<T>(IEnumerable<T> l, Func<T, string> f) {
      return Comma(",", l, f);
    }

    public static string Comma<T>(string comma, IEnumerable<T> l, Func<T,string> f) {
      string res = "";
      string c = "";
      foreach(var t in l) {
        res += c + f(t);
        c = comma;
      }
      return res;
    }

    public static List<B> Map<A,B>(IEnumerable<A> xs, Func<A,B> f)
    {
      List<B> ys = new List<B>();
      foreach (A x in xs) {
        ys.Add(f(x));
      }
      return ys;
    }

    public static List<A> Nil<A>() {
      return new List<A>();
    }

    public static List<A> Singleton<A>(A x) {
      return new List<A> { x };
    }

    public static List<A> Cons<A>(A x, List<A> xs) {
      return Concat(Singleton(x), xs);
    }

    public static List<A> Snoc<A>(List<A> xs, A x) {
      return Concat(xs, Singleton(x));
    }

    public static List<A> Concat<A>(List<A> xs, List<A> ys) {
      List<A> cpy = new List<A>(xs);
      cpy.AddRange(ys);
      return cpy;
    }

    public static Dictionary<A,B> Dict<A,B>(IEnumerable<A> xs, IEnumerable<B> ys) {
      return Dict<A,B>(xs.Zip(ys)); 
    }

    public static Dictionary<A,B> Dict<A,B>(IEnumerable<Tuple<A,B>> xys) {
      Dictionary<A,B> res = new Dictionary<A,B>();
      foreach (var p in xys) {
        res[p.Item1] = p.Item2; 
      }
      return res;
    }

  }
}
