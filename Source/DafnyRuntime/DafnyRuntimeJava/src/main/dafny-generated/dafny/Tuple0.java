package dafny;

@SuppressWarnings({"unchecked", "deprecation"})
public class Tuple0 {

  public Tuple0() {
  }

  private static final dafny.TypeDescriptor<Tuple0> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(Tuple0.class, () -> Default());
  public static dafny.TypeDescriptor<Tuple0> _typeDescriptor() {
    return (dafny.TypeDescriptor<Tuple0>) (dafny.TypeDescriptor<?>) _TYPE;
  }

  public static Tuple0 Default() {
    return create();
  }

  public static Tuple0 create() {
    return new Tuple0();
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    Tuple0 o = (Tuple0) obj;
    return true;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("(");
    sb.append(")");
    return sb.toString();
  }

  @Override
  public int hashCode() {
    // GetHashCode method (Uses the djb2 algorithm)
    // https://stackoverflow.com/questions/1579721/why-are-5381-and-33-so-important-in-the-djb2-algorithm
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int)hash;
  }
}
