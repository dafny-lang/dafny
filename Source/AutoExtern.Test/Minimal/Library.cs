namespace NS;

public interface Intf {
  public string Prop { get; }
}

public class Impl : Intf {
  public int Field;
  public string Prop => Field.ToString();
}
