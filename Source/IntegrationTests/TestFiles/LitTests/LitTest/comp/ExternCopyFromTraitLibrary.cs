namespace M {
  public partial class C1 : T1 {
    public void m1_ext() {
    }
  }
}

namespace M1 {
  public interface Asker {
    public void Exclaim();
    public void Speak() {
      System.Console.WriteLine("Hello, I wish to have...");
      Exclaim();
    }
  }
}
