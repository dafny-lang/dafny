// RUN: %dafny /compileVerbose:1 /compile:2 /spillTargetCode:3 /compileTarget:java /noVerify "%s" > "%t"

include "JavaMocks.dfy"
include "Utils.dfy"

module JavaMocksTests {

  import opened JavaMocks
  import opened Utils

  class EvenTests {

    method {:extern} {:fresh} freshEven() returns (e:Even) ensures fresh(e)

    method {:test} PassingTestUsingFresh() {
        var e:Even := freshEven();
        e.value := 4;
        Assertions.assertEquals(e.value % 2, 0);
    }

    method {:test} FailingTestUsingFresh() {
        var e:Even := freshEven();
        e.value := 5;
        Assertions<bool>.assertFalse(e.value % 2 == 0);
    }

    method {:extern} {:mock} MockValidEven() returns (e:Even) 
        ensures fresh(e) 
        ensures e.IsValid() == true

    method {:extern} {:mock} MockInValidEven() returns (e:Even) 
        ensures fresh(e) 
        ensures e.IsValid() == false

    method {:test} PassingTestUsingValidMock() {
        var e:Even := MockValidEven();
        Assertions<bool>.assertTrue(e.IsValid());
    }

    method {:test} PassingTestUsingInValidMock() {
        var e:Even := MockInValidEven();
        Assertions<bool>.assertFalse(e.IsValid());
    }

    method {:extern} {:mock} MockSum() returns (e:Even) 
        ensures fresh(e) 
        ensures e.Sum(2, 2) == 3

    method {:test} PassingMockSum() {
        var e:Even := MockSum();
        Assertions<bool>.assertTrue(e.Sum(2, 2) == 3);
    }

    method {:extern} {:mock} MockSumForall() returns (e:Even) 
    ensures fresh(e) 
    ensures forall a:int, b:int :: e.Sum(a, b) == 3

    method {:test} PassingTestMockForall() {
        var e:Even := MockSumForall();
        Assertions<bool>.assertTrue(e.Sum(2, 2) == 3);
        Assertions<bool>.assertTrue(e.Sum(3, 2) == 3);
        Assertions.assertEquals(e.Sum(100, 3), 3);
    }

    method {:extern} {:mock} MockSumAsMultiplication() returns (e:Even) 
        ensures fresh(e) 
        ensures forall a:int :: e.Sum(3, a) == a * 3
        
    method {:test} PassingTestMockSumAsMultiplication() {
        var e:Even := MockSumAsMultiplication();
        Assertions<bool>.assertTrue(e.Sum(3, 2) == 6);
        Assertions<bool>.assertTrue(e.Sum(3, 0) == 0);
    }

    // method {:extern} {:mock} ParametrizedMock(a: int) returns (e:Even) 
    //     ensures fresh(e) 
    //     ensures e.value == a;
        
    // method {:test} PassingParameterizedMock() {
    //     var e:Even := ParametrizedMock(24);
    //     expect(e.value == 24);
    //     expect(e.value != 7);
    // }
  }
}