using System;
using Xunit;
using Dafny;

namespace DafnyRuntime.Tests {
  public class TupleTests {

    public Func<int, int> C = (int i) => i;
    public Dafny.TypeDescriptor<int> D = new Dafny.TypeDescriptor<int>(0);

    [Fact]
    public void TestTuple2() {
      var t = new _System.Tuple2<int, int>(0, 1);
      Assert.Equal(t, t.DowncastClone(C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1)", t.ToString());
      Assert.Equal(t, _System.Tuple2<int, int>.Default(0, 1));
      Assert.Equal(t, _System.Tuple2<int, int>.create____hMake2(0, 1));
      Assert.Equal(_System.Tuple2<int, int>.create(0, 0), _System.Tuple2<int, int>._TypeDescriptor(D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
    }

    // I am grateful for LLMs to generate all these tests.
    [Fact]
    public void TestTuple3() {
      var t = new _System.Tuple3<int, int, int>(0, 1, 2);
      Assert.Equal(t, t.DowncastClone(C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2)", t.ToString());
      Assert.Equal(t, _System.Tuple3<int, int, int>.Default(0, 1, 2));
      Assert.Equal(t, _System.Tuple3<int, int, int>.create____hMake3(0, 1, 2));
      Assert.Equal(_System.Tuple3<int, int, int>.create(0, 0, 0),
        _System.Tuple3<int, int, int>._TypeDescriptor(D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
    }

    [Fact]
    public void TestTuple4() {
      var t = new _System.Tuple4<int, int, int, int>(0, 1, 2, 3);
      Assert.Equal(t, t.DowncastClone(C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3)", t.ToString());
      Assert.Equal(t, _System.Tuple4<int, int, int, int>.Default(0, 1, 2, 3));
      Assert.Equal(t, _System.Tuple4<int, int, int, int>.create____hMake4(0, 1, 2, 3));
      Assert.Equal(_System.Tuple4<int, int, int, int>.create(0, 0, 0, 0),
        _System.Tuple4<int, int, int, int>._TypeDescriptor(D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
    }

    [Fact]
    public void TestTuple5() {
      var t = new _System.Tuple5<int, int, int, int, int>(0, 1, 2, 3, 4);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4)", t.ToString());
      Assert.Equal(t, _System.Tuple5<int, int, int, int, int>.Default(0, 1, 2, 3, 4));
      Assert.Equal(t, _System.Tuple5<int, int, int, int, int>.create____hMake5(0, 1, 2, 3, 4));
      Assert.Equal(_System.Tuple5<int, int, int, int, int>.create(0, 0, 0, 0, 0),
        _System.Tuple5<int, int, int, int, int>._TypeDescriptor(D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
    }

    [Fact]
    public void TestTuple6() {
      var t = new _System.Tuple6<int, int, int, int, int, int>(0, 1, 2, 3, 4, 5);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5)", t.ToString());
      Assert.Equal(t, _System.Tuple6<int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5));
      Assert.Equal(t, _System.Tuple6<int, int, int, int, int, int>.create____hMake6(0, 1, 2, 3, 4, 5));
      Assert.Equal(_System.Tuple6<int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0),
        _System.Tuple6<int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
    }

    [Fact]
    public void TestTuple7() {
      var t = new _System.Tuple7<int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6)", t.ToString());
      Assert.Equal(t, _System.Tuple7<int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6));
      Assert.Equal(t, _System.Tuple7<int, int, int, int, int, int, int>.create____hMake7(0, 1, 2, 3, 4, 5, 6));
      Assert.Equal(_System.Tuple7<int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0),
        _System.Tuple7<int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
    }

    [Fact]
    public void TestTuple8() {
      var t = new _System.Tuple8<int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7)", t.ToString());
      Assert.Equal(t, _System.Tuple8<int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7));
      Assert.Equal(t, _System.Tuple8<int, int, int, int, int, int, int, int>.create____hMake8(0, 1, 2, 3, 4, 5, 6, 7));
      Assert.Equal(_System.Tuple8<int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple8<int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
    }

    [Fact]
    public void TestTuple9() {
      var t = new _System.Tuple9<int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8)", t.ToString());
      Assert.Equal(t, _System.Tuple9<int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8));
      Assert.Equal(t, _System.Tuple9<int, int, int, int, int, int, int, int, int>.create____hMake9(0, 1, 2, 3, 4, 5, 6, 7, 8));
      Assert.Equal(_System.Tuple9<int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple9<int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
    }

    [Fact]
    public void TestTuple10() {
      var t = new _System.Tuple10<int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9)", t.ToString());
      Assert.Equal(t, _System.Tuple10<int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));
      Assert.Equal(t, _System.Tuple10<int, int, int, int, int, int, int, int, int, int>.create____hMake10(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));
      Assert.Equal(_System.Tuple10<int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple10<int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
    }

    [Fact]
    public void TestTuple11() {
      var t = new _System.Tuple11<int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)", t.ToString());
      Assert.Equal(t, _System.Tuple11<int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10));
      Assert.Equal(t, _System.Tuple11<int, int, int, int, int, int, int, int, int, int, int>.create____hMake11(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10));
      Assert.Equal(_System.Tuple11<int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple11<int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
    }

    [Fact]
    public void TestTuple12() {
      var t = new _System.Tuple12<int, int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)", t.ToString());
      Assert.Equal(t, _System.Tuple12<int, int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11));
      Assert.Equal(t, _System.Tuple12<int, int, int, int, int, int, int, int, int, int, int, int>.create____hMake12(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11));
      Assert.Equal(_System.Tuple12<int, int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple12<int, int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
      Assert.Equal(11, t.dtor__11);
    }

    [Fact]
    public void TestTuple13() {
      var t = new _System.Tuple13<int, int, int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)", t.ToString());
      Assert.Equal(t, _System.Tuple13<int, int, int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12));
      Assert.Equal(t, _System.Tuple13<int, int, int, int, int, int, int, int, int, int, int, int, int>.create____hMake13(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12));
      Assert.Equal(_System.Tuple13<int, int, int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple13<int, int, int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
      Assert.Equal(11, t.dtor__11);
      Assert.Equal(12, t.dtor__12);
    }

    [Fact]
    public void TestTuple14() {
      var t = new _System.Tuple14<int, int, int, int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13)", t.ToString());
      Assert.Equal(t, _System.Tuple14<int, int, int, int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13));
      Assert.Equal(t, _System.Tuple14<int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create____hMake14(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13));
      Assert.Equal(_System.Tuple14<int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple14<int, int, int, int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
      Assert.Equal(11, t.dtor__11);
      Assert.Equal(12, t.dtor__12);
      Assert.Equal(13, t.dtor__13);
    }

    [Fact]
    public void TestTuple15() {
      var t = new _System.Tuple15<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14)", t.ToString());
      Assert.Equal(t, _System.Tuple15<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14));
      Assert.Equal(t, _System.Tuple15<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create____hMake15(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14));
      Assert.Equal(_System.Tuple15<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple15<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
      Assert.Equal(11, t.dtor__11);
      Assert.Equal(12, t.dtor__12);
      Assert.Equal(13, t.dtor__13);
      Assert.Equal(14, t.dtor__14);
    }
    [Fact]
    public void TestTuple16() {
      var t = new _System.Tuple16<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)", t.ToString());
      Assert.Equal(t, _System.Tuple16<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15));
      Assert.Equal(t, _System.Tuple16<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create____hMake16(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15));
      Assert.Equal(_System.Tuple16<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple16<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
      Assert.Equal(11, t.dtor__11);
      Assert.Equal(12, t.dtor__12);
      Assert.Equal(13, t.dtor__13);
      Assert.Equal(14, t.dtor__14);
      Assert.Equal(15, t.dtor__15);
    }

    [Fact]
    public void TestTuple17() {
      var t = new _System.Tuple17<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16)", t.ToString());
      Assert.Equal(t, _System.Tuple17<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16));
      Assert.Equal(t, _System.Tuple17<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create____hMake17(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16));
      Assert.Equal(_System.Tuple17<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple17<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
      Assert.Equal(11, t.dtor__11);
      Assert.Equal(12, t.dtor__12);
      Assert.Equal(13, t.dtor__13);
      Assert.Equal(14, t.dtor__14);
      Assert.Equal(15, t.dtor__15);
      Assert.Equal(16, t.dtor__16);
    }

    [Fact]
    public void TestTuple18() {
      var t = new _System.Tuple18<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17)", t.ToString());
      Assert.Equal(t, _System.Tuple18<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17));
      Assert.Equal(t, _System.Tuple18<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create____hMake18(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17));
      Assert.Equal(_System.Tuple18<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple18<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
      Assert.Equal(11, t.dtor__11);
      Assert.Equal(12, t.dtor__12);
      Assert.Equal(13, t.dtor__13);
      Assert.Equal(14, t.dtor__14);
      Assert.Equal(15, t.dtor__15);
      Assert.Equal(16, t.dtor__16);
      Assert.Equal(17, t.dtor__17);
    }

    [Fact]
    public void TestTuple19() {
      var t = new _System.Tuple19<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18)", t.ToString());
      Assert.Equal(t, _System.Tuple19<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18));
      Assert.Equal(t, _System.Tuple19<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create____hMake19(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18));
      Assert.Equal(_System.Tuple19<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple19<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
      Assert.Equal(11, t.dtor__11);
      Assert.Equal(12, t.dtor__12);
      Assert.Equal(13, t.dtor__13);
      Assert.Equal(14, t.dtor__14);
      Assert.Equal(15, t.dtor__15);
      Assert.Equal(16, t.dtor__16);
      Assert.Equal(17, t.dtor__17);
      Assert.Equal(18, t.dtor__18);
    }

    [Fact]
    public void TestTuple20() {
      var t = new _System.Tuple20<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19);
      Assert.Equal(t, t.DowncastClone(C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C));
      Assert.NotEqual(0, t.GetHashCode());
      Assert.Equal("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19)", t.ToString());
      Assert.Equal(t, _System.Tuple20<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.Default(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19));
      Assert.Equal(t, _System.Tuple20<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create____hMake20(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19));
      Assert.Equal(_System.Tuple20<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>.create(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
          _System.Tuple20<int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int, int>._TypeDescriptor(D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D, D).Default());
      Assert.Equal(0, t.dtor__0);
      Assert.Equal(1, t.dtor__1);
      Assert.Equal(2, t.dtor__2);
      Assert.Equal(3, t.dtor__3);
      Assert.Equal(4, t.dtor__4);
      Assert.Equal(5, t.dtor__5);
      Assert.Equal(6, t.dtor__6);
      Assert.Equal(7, t.dtor__7);
      Assert.Equal(8, t.dtor__8);
      Assert.Equal(9, t.dtor__9);
      Assert.Equal(10, t.dtor__10);
      Assert.Equal(11, t.dtor__11);
      Assert.Equal(12, t.dtor__12);
      Assert.Equal(13, t.dtor__13);
      Assert.Equal(14, t.dtor__14);
      Assert.Equal(15, t.dtor__15);
      Assert.Equal(16, t.dtor__16);
      Assert.Equal(17, t.dtor__17);
      Assert.Equal(18, t.dtor__18);
      Assert.Equal(19, t.dtor__19);
    }

  }
}
