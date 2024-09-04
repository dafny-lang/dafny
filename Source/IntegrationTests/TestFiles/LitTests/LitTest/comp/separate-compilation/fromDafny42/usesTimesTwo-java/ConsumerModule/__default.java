// Class __default
// Dafny class __default compiled into Java
package ConsumerModule;


@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void Main(dafny.DafnySequence<? extends dafny.DafnySequence<? extends dafny.CodePoint>> __noArgsParameter)
  {
    java.math.BigInteger _0_n = java.math.BigInteger.ZERO;
    _0_n = java.math.BigInteger.valueOf(21L);
    java.math.BigInteger _1_TwoN = java.math.BigInteger.ZERO;
    _1_TwoN = CoolLibraryName_mLibraryModule.__default.TimesTwo(_0_n);
    System.out.print((dafny.DafnySequence.asUnicodeString("Two times ")).verbatimString());
    System.out.print(java.lang.String.valueOf(_0_n));
    System.out.print((dafny.DafnySequence.asUnicodeString(" is ")).verbatimString());
    System.out.print(java.lang.String.valueOf(_1_TwoN));
    System.out.print((dafny.DafnySequence.asUnicodeString("\n")).verbatimString());
    java.math.BigInteger _2_aNat = java.math.BigInteger.ZERO;
    java.math.BigInteger _out0 = java.math.BigInteger.ZERO;
    _out0 = __default.PickANat();
    _2_aNat = _out0;
  }
  public static void __Main(dafny.DafnySequence<? extends dafny.DafnySequence<? extends dafny.CodePoint>> args) {
    __default.Main(args);
  }
  public static java.math.BigInteger PickANat()
  {
    java.math.BigInteger n = java.math.BigInteger.ZERO;
    if(true) {
      java.math.BigInteger _out1 = java.math.BigInteger.ZERO;
      _out1 = __default.<java.math.BigInteger>PickSomething(_System.nat._typeDescriptor());
      n = _out1;
    }
    return n;
  }
  public static <__T> __T PickSomething(dafny.TypeDescriptor<__T> _td___T)
  {
    @SuppressWarnings({"unchecked", "deprecation"})
    __T t = _td___T.defaultValue();
    if(true) {
    }
    return t;
  }
  public static void MakeAResult()
  {
    CoolLibraryName_mLibraryModule.Result<java.math.BigInteger, dafny.DafnySequence<? extends dafny.CodePoint>> _3_r;
    _3_r = CoolLibraryName_mLibraryModule.Result.<java.math.BigInteger, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(java.math.BigInteger.valueOf(42L));
  }
  public static void MakeAPair()
  {
    CoolLibraryName_mLibraryModule.Pair<java.math.BigInteger, dafny.DafnySequence<? extends dafny.CodePoint>> _4_p;
    _4_p = CoolLibraryName_mLibraryModule.Pair.<java.math.BigInteger, dafny.DafnySequence<? extends dafny.CodePoint>>create(java.math.BigInteger.ONE, dafny.DafnySequence.asUnicodeString("partridge in a pair tree"));
  }
  @Override
  public java.lang.String toString() {
    return "ConsumerModule._default";
  }
}
