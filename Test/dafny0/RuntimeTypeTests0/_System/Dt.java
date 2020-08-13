// Class Dt<A>
// Dafny class Dt<A> compiled into Java
package _System;


@SuppressWarnings({"unchecked", "deprecation"})
public class Dt<A> {
  public A get;
  public Dt (A get) {
    this.get = get;
  }
  public Dt() { }
  
  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Dt<A> o = (Dt<A>)other;
    return java.util.Objects.equals(this.get, o.get);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this.get);
    return (int)hash;
  }
  
  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Dt.Atom");
    s.append("(");
    s.append(this.get == null ? "" : this.get);
    s.append(")");
    return s.toString();
  }
  
  public static <A> Dt<A> Default(dafny.Type<A> _td_A) {
    return new Dt<>(_td_A.defaultValue());
  }
  public static <A> dafny.Type<Dt<A>> _type(dafny.Type<A> _td_A) {
    return (dafny.Type<Dt<A>>) (dafny.Type<?>) dafny.Type.referenceWithInitializer(Dt.class, () -> Default(_td_A));
  }
  public boolean is_Atom() { return true; }
  public A dtor_get() {
    return this.get;
  }
}
