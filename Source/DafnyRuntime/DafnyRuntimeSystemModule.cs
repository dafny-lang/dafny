// Dafny program systemModulePopulator.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.3.0.0
// Command-line arguments: translate cs --no-verify --use-basename-for-filename --include-system-module systemModulePopulator.dfy --output:systemModulePopulator
// systemModulePopulator.dfy

method HasTuples()
{
  var has0 := ();
  var has1 := 1;
  var has2 := (1, 2);
  var has3 := (1, 2, 3);
  var has4 := (1, 2, 3, 4);
  var has5 := (1, 2, 3, 4, 5);
  var has6 := (1, 2, 3, 4, 5, 6);
  var has7 := (1, 2, 3, 4, 5, 6, 7);
  var has8 := (1, 2, 3, 4, 5, 6, 7, 8);
  var has9 := (1, 2, 3, 4, 5, 6, 7, 8, 9);
  var has10 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
  var has11 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11);
  var has12 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
  var has13 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);
  var has14 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14);
  var has15 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
  var has16 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
  var has17 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17);
  var has18 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18);
  var has19 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19);
  var has20 := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20);
}

method HasArrows()
{
  var has0 := () => 42;
  var has1 := (x1: int) => 42;
  var has2 := (x1: int, x2: int) => 42;
  var has3 := (x1: int, x2: int, x3: int) => 42;
  var has4 := (x1: int, x2: int, x3: int, x4: int) => 42;
}

method HasArrays()
{
  var has1 := new int[1];
  var has2 := new int[1, 2];
  var has3 := new int[1, 2, 3];
  var has4 := new int[1, 2, 3, 4];
}
")]

namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace _module {

  public partial class __default {
    public static void HasTuples()
    {
      _System._ITuple0 _0_has0;
      _0_has0 = _System.Tuple0.create();
      BigInteger _1_has1;
      _1_has1 = BigInteger.One;
      _System._ITuple2<BigInteger, BigInteger> _2_has2;
      _2_has2 = _System.Tuple2<BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2));
      _System._ITuple3<BigInteger, BigInteger, BigInteger> _3_has3;
      _3_has3 = _System.Tuple3<BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3));
      _System._ITuple4<BigInteger, BigInteger, BigInteger, BigInteger> _4_has4;
      _4_has4 = _System.Tuple4<BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4));
      _System._ITuple5<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _5_has5;
      _5_has5 = _System.Tuple5<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5));
      _System._ITuple6<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _6_has6;
      _6_has6 = _System.Tuple6<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6));
      _System._ITuple7<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _7_has7;
      _7_has7 = _System.Tuple7<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7));
      _System._ITuple8<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _8_has8;
      _8_has8 = _System.Tuple8<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8));
      _System._ITuple9<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _9_has9;
      _9_has9 = _System.Tuple9<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9));
      _System._ITuple10<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _10_has10;
      _10_has10 = _System.Tuple10<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10));
      _System._ITuple11<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _11_has11;
      _11_has11 = _System.Tuple11<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11));
      _System._ITuple12<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _12_has12;
      _12_has12 = _System.Tuple12<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11), new BigInteger(12));
      _System._ITuple13<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _13_has13;
      _13_has13 = _System.Tuple13<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11), new BigInteger(12), new BigInteger(13));
      _System._ITuple14<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _14_has14;
      _14_has14 = _System.Tuple14<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11), new BigInteger(12), new BigInteger(13), new BigInteger(14));
      _System._ITuple15<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _15_has15;
      _15_has15 = _System.Tuple15<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11), new BigInteger(12), new BigInteger(13), new BigInteger(14), new BigInteger(15));
      _System._ITuple16<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _16_has16;
      _16_has16 = _System.Tuple16<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11), new BigInteger(12), new BigInteger(13), new BigInteger(14), new BigInteger(15), new BigInteger(16));
      _System._ITuple17<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _17_has17;
      _17_has17 = _System.Tuple17<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11), new BigInteger(12), new BigInteger(13), new BigInteger(14), new BigInteger(15), new BigInteger(16), new BigInteger(17));
      _System._ITuple18<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _18_has18;
      _18_has18 = _System.Tuple18<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11), new BigInteger(12), new BigInteger(13), new BigInteger(14), new BigInteger(15), new BigInteger(16), new BigInteger(17), new BigInteger(18));
      _System._ITuple19<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _19_has19;
      _19_has19 = _System.Tuple19<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11), new BigInteger(12), new BigInteger(13), new BigInteger(14), new BigInteger(15), new BigInteger(16), new BigInteger(17), new BigInteger(18), new BigInteger(19));
      _System._ITuple20<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _20_has20;
      _20_has20 = _System.Tuple20<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>.create(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8), new BigInteger(9), new BigInteger(10), new BigInteger(11), new BigInteger(12), new BigInteger(13), new BigInteger(14), new BigInteger(15), new BigInteger(16), new BigInteger(17), new BigInteger(18), new BigInteger(19), new BigInteger(20));
    }
    public static void HasArrows()
    {
      Func<BigInteger> _21_has0;
      _21_has0 = ((System.Func<BigInteger>)(() => {
        return new BigInteger(42);
      }));
      Func<BigInteger, BigInteger> _22_has1;
      _22_has1 = ((System.Func<BigInteger, BigInteger>)((_23_x1) => {
        return new BigInteger(42);
      }));
      Func<BigInteger, BigInteger, BigInteger> _24_has2;
      _24_has2 = ((System.Func<BigInteger, BigInteger, BigInteger>)((_25_x1, _26_x2) => {
        return new BigInteger(42);
      }));
      Func<BigInteger, BigInteger, BigInteger, BigInteger> _27_has3;
      _27_has3 = ((System.Func<BigInteger, BigInteger, BigInteger, BigInteger>)((_28_x1, _29_x2, _30_x3) => {
        return new BigInteger(42);
      }));
      Func<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger> _31_has4;
      _31_has4 = ((System.Func<BigInteger, BigInteger, BigInteger, BigInteger, BigInteger>)((_32_x1, _33_x2, _34_x3, _35_x4) => {
        return new BigInteger(42);
      }));
    }
    public static void HasArrays()
    {
      BigInteger[] _36_has1;
      BigInteger[] _nw0 = new BigInteger[Dafny.Helpers.ToIntChecked(BigInteger.One, "array size exceeds memory limit")];
      _36_has1 = _nw0;
      BigInteger[,] _37_has2;
      BigInteger[,] _nw1 = new BigInteger[Dafny.Helpers.ToIntChecked(BigInteger.One, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(new BigInteger(2), "array size exceeds memory limit")];
      _37_has2 = _nw1;
      BigInteger[,,] _38_has3;
      BigInteger[,,] _nw2 = new BigInteger[Dafny.Helpers.ToIntChecked(BigInteger.One, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(new BigInteger(2), "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(new BigInteger(3), "array size exceeds memory limit")];
      _38_has3 = _nw2;
      BigInteger[,,,] _39_has4;
      BigInteger[,,,] _nw3 = new BigInteger[Dafny.Helpers.ToIntChecked(BigInteger.One, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(new BigInteger(2), "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(new BigInteger(3), "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(new BigInteger(4), "array size exceeds memory limit")];
      _39_has4 = _nw3;
    }
  }
} // end of namespace _module
