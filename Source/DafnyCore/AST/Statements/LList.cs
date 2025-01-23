namespace Microsoft.Dafny;

public class LList<T>(T d, LList<T> next) {
  public readonly T Data = d;
  public readonly LList<T> Next = next;

  public static LList<T> Append(LList<T> a, LList<T> b) {
    if (a == null) {
      return b;
    }

    return new LList<T>(a.Data, Append(a.Next, b));
    // pretend this is ML
  }
  public static int Count(LList<T> n) {
    int count = 0;
    while (n != null) {
      count++;
      n = n.Next;
    }
    return count;
  }
}