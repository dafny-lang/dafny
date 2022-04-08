using System.Numerics;

namespace CSharpInterop {
  public partial class ListUtils {
    public static List<T> Mk<T>() => new List<T>();

    public static void Append<T>(List<T> l, T t) => l.Add(t);

    public static B FoldL<A, B>(Func<B, A, B> f, B b0, List<A> lA) {
      for (int i = 0; i < lA.Count; i++) {
        b0 = f(b0, lA[i]);
      }
      return b0;
    }

    public static B FoldR<A, B>(Func<A, B, B> f, B b0, List<A> lA) {
      for (int i = lA.Count - 1; i >= 0; i--) {
        b0 = f(lA[i], b0);
      }
      return b0;
    }
  }
}
