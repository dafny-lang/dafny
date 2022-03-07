// Class Even
// Dafny class Even compiled into Java
package JavaMocks_Compile;


@SuppressWarnings({"unchecked", "deprecation"})
public class Even {
  public Even() {
    this.value = java.math.BigInteger.ZERO;
  }
  public java.math.BigInteger value;
  public boolean IsValid() {
    return (dafny.DafnyEuclidean.EuclideanModulus(this.value, java.math.BigInteger.valueOf(2L))).signum() == 0;
  }
  public void __ctor(java.math.BigInteger value)
  {
    (this).value = value;
  }
  public java.math.BigInteger Sum(java.math.BigInteger a, java.math.BigInteger b)
  {
    return (a).add((b));
  }
  private static final dafny.TypeDescriptor<Even> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(Even.class, () -> (Even) null);
  public static dafny.TypeDescriptor<Even> _typeDescriptor() {
    return (dafny.TypeDescriptor<Even>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
