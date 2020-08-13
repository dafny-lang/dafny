// Class Class1
// Dafny class Class1 compiled into Java
package _System;


@SuppressWarnings({"unchecked", "deprecation"})
public class Class1 implements Tr {
  public Class1() {
    this._u = 'D';
    this.y = dafny.BigRational.ZERO;
  }
  public char _u;
  public char u()
  {
    return this._u;
  }
  public void set_u(char value)
  {
    this._u = value;
  }
  public dafny.BigRational y;
  private static final dafny.Type<Class1> _TYPE = dafny.Type.referenceWithInitializer(Class1.class, () -> (Class1) null);
  public static dafny.Type<Class1> _type() {
    return (dafny.Type<Class1>) (dafny.Type<?>) _TYPE;
  }
}
