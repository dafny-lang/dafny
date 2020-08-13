// Class __default
// Dafny class __default compiled into Java
package _System;


@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void G()
  {
    dafny.DafnySet<java.math.BigInteger> _39_s = dafny.DafnySet.<java.math.BigInteger> empty();
    dafny.DafnySet<java.math.BigInteger> _40_t = dafny.DafnySet.<java.math.BigInteger> empty();
    _39_s = dafny.DafnySet.of(java.math.BigInteger.valueOf(5L), java.math.BigInteger.valueOf(7L));
    _40_t = _39_s;
    _39_s = _40_t;
    System.out.print(String.valueOf(_39_s));
    System.out.print(dafny.DafnySequence.asString(" and ").verbatimString());
    System.out.print(String.valueOf(_40_t));
    System.out.print(dafny.DafnySequence.asString("\n").verbatimString());
  }
  public static void H()
  {
    Class0 _41_c;
    Class0 _nw0 = new Class0();
    _41_c = _nw0;
    Dt<Class0> _42_a;
    _42_a = new Dt<>(_41_c);
    /* Compilation error: compilation does not support trait types as a type parameter; consider introducing a ghost */
    Dt<Object> _43_b = Dt.<Object>Default(dafny.Type.OBJECT);
    _43_b = _42_a;
    System.out.print(String.valueOf(_42_a));
    System.out.print(dafny.DafnySequence.asString(" and ").verbatimString());
    System.out.print(String.valueOf(_43_b));
    System.out.print(dafny.DafnySequence.asString("\n").verbatimString());
  }
  public static void I()
  {
    Class0 _44_c;
    Class0 _nw1 = new Class0();
    _44_c = _nw1;
    Dt<Class0> _45_a;
    _45_a = new Dt<>(_44_c);
    /* Compilation error: compilation does not support trait types as a type parameter; consider introducing a ghost */
    Dt<Object> _46_b = Dt.<Object>Default(dafny.Type.OBJECT);
    _46_b = _45_a;
    System.out.print(String.valueOf(_45_a));
    System.out.print(dafny.DafnySequence.asString(" and ").verbatimString());
    System.out.print(String.valueOf(_46_b));
    System.out.print(dafny.DafnySequence.asString("\n").verbatimString());
  }
  public static void J()
  {
    Class0 _47_c0;
    Class0 _nw2 = new Class0();
    _47_c0 = _nw2;
    Class1 _48_c1;
    Class1 _nw3 = new Class1();
    _48_c1 = _nw3;
    dafny.DafnySet<? extends Tr> _49_s;
    _49_s = dafny.DafnySet.of(_47_c0, _48_c1);
    dafny.DafnySet<Class0> _50_t;
    _50_t = dafny.DafnySet.of(_47_c0);
    _49_s = _50_t;
    System.out.print(String.valueOf(_49_s));
    System.out.print(dafny.DafnySequence.asString(" and ").verbatimString());
    System.out.print(String.valueOf(_50_t));
    System.out.print(dafny.DafnySequence.asString("\n").verbatimString());
  }
  public static void K()
  {
    Class0 _51_c0;
    Class0 _nw4 = new Class0();
    _51_c0 = _nw4;
    Class1 _52_c1;
    Class1 _nw5 = new Class1();
    _52_c1 = _nw5;
    dafny.DafnySequence<? extends Tr> _53_s;
    _53_s = dafny.DafnySequence.of(_Companion_Tr._type(), _51_c0, _52_c1);
    dafny.DafnySequence<Class0> _54_t;
    _54_t = dafny.DafnySequence.of(Class0._type(), _51_c0);
    _53_s = _54_t;
    System.out.print(String.valueOf(_53_s));
    System.out.print(dafny.DafnySequence.asString(" and ").verbatimString());
    System.out.print(String.valueOf(_54_t));
    System.out.print(dafny.DafnySequence.asString("\n").verbatimString());
  }
  public static void L()
  {
    Class0 _55_c0;
    Class0 _nw6 = new Class0();
    _55_c0 = _nw6;
    Class1 _56_c1;
    Class1 _nw7 = new Class1();
    _56_c1 = _nw7;
    dafny.DafnyMultiset<? extends Tr> _57_s;
    _57_s = dafny.DafnyMultiset.of(_55_c0, _56_c1);
    dafny.DafnyMultiset<Class0> _58_t;
    _58_t = dafny.DafnyMultiset.of(_55_c0);
    _57_s = _58_t;
    System.out.print(String.valueOf(_57_s));
    System.out.print(dafny.DafnySequence.asString(" and ").verbatimString());
    System.out.print(String.valueOf(_58_t));
    System.out.print(dafny.DafnySequence.asString("\n").verbatimString());
  }
  public static void M()
  {
    Class0 _59_c0;
    Class0 _nw8 = new Class0();
    _59_c0 = _nw8;
    Class1 _60_c1;
    Class1 _nw9 = new Class1();
    _60_c1 = _nw9;
    dafny.DafnyMap<java.math.BigInteger, ? extends Tr> _61_s;
    _61_s = dafny.DafnyMap.fromElements(new dafny.Tuple2(java.math.BigInteger.valueOf(8L), _59_c0), new dafny.Tuple2(java.math.BigInteger.valueOf(9L), _60_c1));
    dafny.DafnyMap<java.math.BigInteger, Class0> _62_t;
    _62_t = dafny.DafnyMap.fromElements(new dafny.Tuple2(java.math.BigInteger.valueOf(7L), _59_c0));
    _61_s = _62_t;
    System.out.print(String.valueOf(_61_s));
    System.out.print(dafny.DafnySequence.asString(" and ").verbatimString());
    System.out.print(String.valueOf(_62_t));
    System.out.print(dafny.DafnySequence.asString("\n").verbatimString());
  }
  public static void Downcast()
  {
    Class0 _63_c0;
    Class0 _nw10 = new Class0();
    _63_c0 = _nw10;
    dafny.DafnySequence<Class0> _64_s;
    _64_s = dafny.DafnySequence.of(Class0._type(), _63_c0, _63_c0);
    dafny.DafnySequence<? extends Tr> _65_t;
    _65_t = _64_s;
    _65_t = _64_s;
    System.out.print(String.valueOf(_64_s));
    System.out.print(dafny.DafnySequence.asString(" and ").verbatimString());
    System.out.print(String.valueOf(_65_t));
    System.out.print(dafny.DafnySequence.asString("\n").verbatimString());
  }
  public static void Main()
  {
    __default.G();
    __default.H();
    __default.I();
    __default.J();
    __default.K();
    __default.L();
    __default.M();
    __default.Downcast();
  }
  private static final dafny.Type<__default> _TYPE = dafny.Type.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.Type<__default> _type() {
    return (dafny.Type<__default>) (dafny.Type<?>) _TYPE;
  }
}
