namespace M {
  // try an unusual type here, namely a struct
  public struct T {
  }

  public partial class __default {
    public static T GetT() {
      return new T();
    }
  }

  // By declaring U a class here, it allows "null" as a value.
  // In other words, the opaque type M.U declared in the Dafny program
  // evidently stands for what in Dafny could have been declared as
  // type U? for a class U.
  public class U {
  }

  public struct V {
  }

  public struct W<A> {
  }
}
