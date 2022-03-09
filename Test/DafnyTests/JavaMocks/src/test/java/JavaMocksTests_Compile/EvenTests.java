// Class EvenTests
// Dafny class EvenTests compiled into Java
package JavaMocksTests_Compile;

import JavaMocks_Compile.*;
import Utils_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class EvenTests {
  public EvenTests() {
  }
  public JavaMocks_Compile.Even freshEven() {
    return new JavaMocks_Compile.Even();
  }
  public void PassingTestUsingFresh()
  {
    JavaMocks_Compile.Even _78_e;
    JavaMocks_Compile.Even _out0;
    _out0 = (this).freshEven();
    _78_e = _out0;
    (_78_e).value = java.math.BigInteger.valueOf(4L);
    Utils_Compile.Assertions.<java.math.BigInteger>assertEquals(dafny.TypeDescriptor.BIG_INTEGER, dafny.DafnyEuclidean.EuclideanModulus(_78_e.value, java.math.BigInteger.valueOf(2L)), java.math.BigInteger.ZERO);
  }
  public void FailingTestUsingFresh()
  {
    JavaMocks_Compile.Even _79_e;
    JavaMocks_Compile.Even _out1;
    _out1 = (this).freshEven();
    _79_e = _out1;
    (_79_e).value = java.math.BigInteger.valueOf(5L);
    Utils_Compile.Assertions.<Boolean>assertFalse(dafny.TypeDescriptor.BOOLEAN, (dafny.DafnyEuclidean.EuclideanModulus(_79_e.value, java.math.BigInteger.valueOf(2L))).signum() == 0);
  }
  public JavaMocks_Compile.Even MockValidEven() {
    JavaMocks_Compile.Even eTmp = org.mockito.Mockito.mock(JavaMocks_Compile.Even.class);
    org.mockito.Mockito.when(eTmp.IsValid()).theReturn(true);
    return eTmp;
  }
  public JavaMocks_Compile.Even MockInValidEven() {
    JavaMocks_Compile.Even eTmp = org.mockito.Mockito.mock(JavaMocks_Compile.Even.class);
    org.mockito.Mockito.when(eTmp.IsValid()).theReturn(false);
    return eTmp;
  }
  public void PassingTestUsingValidMock()
  {
    JavaMocks_Compile.Even _80_e;
    JavaMocks_Compile.Even _out2;
    _out2 = (this).MockValidEven();
    _80_e = _out2;
    Utils_Compile.Assertions.<java.math.BigInteger>assertEquals(dafny.TypeDescriptor.BIG_INTEGER, dafny.DafnyEuclidean.EuclideanModulus(_80_e.value, java.math.BigInteger.valueOf(2L)), java.math.BigInteger.ZERO);
  }
  public void PassingTestUsingInValidMock()
  {
    JavaMocks_Compile.Even _81_e;
    JavaMocks_Compile.Even _out3;
    _out3 = (this).MockInValidEven();
    _81_e = _out3;
    Utils_Compile.Assertions.<Boolean>assertFalse(dafny.TypeDescriptor.BOOLEAN, (dafny.DafnyEuclidean.EuclideanModulus(_81_e.value, java.math.BigInteger.valueOf(2L))).signum() == 0);
  }
  public JavaMocks_Compile.Even MockSum() {
    JavaMocks_Compile.Even eTmp = org.mockito.Mockito.mock(JavaMocks_Compile.Even.class);
    org.mockito.Mockito.when(eTmp.Sum(java.math.BigInteger.valueOf(2L), java.math.BigInteger.valueOf(2L))).theReturn(java.math.BigInteger.valueOf(3L));
    return eTmp;
  }
  public void PassingMockSum()
  {
    JavaMocks_Compile.Even _82_e;
    JavaMocks_Compile.Even _out4;
    _out4 = (this).MockSum();
    _82_e = _out4;
    Utils_Compile.Assertions.<Boolean>assertTrue(dafny.TypeDescriptor.BOOLEAN, java.util.Objects.equals((_82_e).Sum(java.math.BigInteger.valueOf(2L), java.math.BigInteger.valueOf(2L)), java.math.BigInteger.valueOf(3L)));
  }
  public JavaMocks_Compile.Even MockSumForall() {
    JavaMocks_Compile.Even eTmp = org.mockito.Mockito.mock(JavaMocks_Compile.Even.class);
    org.mockito.Mockito.when(eTmp.Sum(org.mockito.Mockito.isA(java.math.BigInteger), org.mockito.Mockito.isA(java.math.BigInteger))).theReturn(java.math.BigInteger.valueOf(3L));
    return eTmp;
  }
  public void PassingTestMockForall()
  {
    JavaMocks_Compile.Even _85_e;
    JavaMocks_Compile.Even _out5;
    _out5 = (this).MockSumForall();
    _85_e = _out5;
    Utils_Compile.Assertions.<Boolean>assertTrue(dafny.TypeDescriptor.BOOLEAN, java.util.Objects.equals((_85_e).Sum(java.math.BigInteger.valueOf(2L), java.math.BigInteger.valueOf(2L)), java.math.BigInteger.valueOf(3L)));
    Utils_Compile.Assertions.<Boolean>assertTrue(dafny.TypeDescriptor.BOOLEAN, java.util.Objects.equals((_85_e).Sum(java.math.BigInteger.valueOf(3L), java.math.BigInteger.valueOf(2L)), java.math.BigInteger.valueOf(3L)));
    Utils_Compile.Assertions.<java.math.BigInteger>assertEquals(dafny.TypeDescriptor.BIG_INTEGER, (_85_e).Sum(java.math.BigInteger.valueOf(100L), java.math.BigInteger.valueOf(3L)), java.math.BigInteger.valueOf(3L));
  }
  public JavaMocks_Compile.Even MockSumAsMultiplication() {
    JavaMocks_Compile.Even eTmp = org.mockito.Mockito.mock(JavaMocks_Compile.Even.class);
    org.mockito.Mockito.when(eTmp.Sum(java.math.BigInteger.valueOf(3L), org.mockito.Mockito.isA(java.math.BigInteger))).theReturn((_86_a).multiply((java.math.BigInteger.valueOf(3L))));
    return eTmp;
  }
  public void PassingTestMockSumAsMultiplication()
  {
    JavaMocks_Compile.Even _87_e;
    JavaMocks_Compile.Even _out6;
    _out6 = (this).MockSumAsMultiplication();
    _87_e = _out6;
    Utils_Compile.Assertions.<Boolean>assertTrue(dafny.TypeDescriptor.BOOLEAN, java.util.Objects.equals((_87_e).Sum(java.math.BigInteger.valueOf(3L), java.math.BigInteger.valueOf(2L)), java.math.BigInteger.valueOf(6L)));
    Utils_Compile.Assertions.<Boolean>assertTrue(dafny.TypeDescriptor.BOOLEAN, ((_87_e).Sum(java.math.BigInteger.valueOf(3L), java.math.BigInteger.ZERO)).signum() == 0);
  }
  public JavaMocks_Compile.Even MockField() {
    JavaMocks_Compile.Even eTmp = org.mockito.Mockito.mock(JavaMocks_Compile.Even.class);
    org.mockito.Mockito.when(eTmp.value).theReturn( java.math.BigInteger.valueOf(7L));
    return eTmp;
  }
  public void PassingMockField()
  {
    JavaMocks_Compile.Even _88_e;
    JavaMocks_Compile.Even _out7;
    _out7 = (this).MockField();
    _88_e = _out7;
    Utils_Compile.Assertions.<Boolean>assertTrue(dafny.TypeDescriptor.BOOLEAN, java.util.Objects.equals(_88_e.value, java.math.BigInteger.valueOf(7L)));
    Utils_Compile.Assertions.<Boolean>assertTrue(dafny.TypeDescriptor.BOOLEAN, !java.util.Objects.equals(_88_e.value, java.math.BigInteger.valueOf(5L)));
  }
  private static final dafny.TypeDescriptor<EvenTests> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(EvenTests.class, () -> (EvenTests) null);
  public static dafny.TypeDescriptor<EvenTests> _typeDescriptor() {
    return (dafny.TypeDescriptor<EvenTests>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
