// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace DAST.Format {

  public partial class __default {
    public static BigInteger SeqToHeight<__T>(Dafny.ISequence<__T> s, Func<__T, BigInteger> f)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        BigInteger _0_i = Dafny.Helpers.Id<Func<__T, BigInteger>>(f)((s).Select(BigInteger.Zero));
        BigInteger _1_j = DAST.Format.__default.SeqToHeight<__T>((s).Drop(BigInteger.One), f);
        if ((_0_i) < (_1_j)) {
          return _1_j;
        } else {
          return _0_i;
        }
      }
    }
  }

  public interface _IUnaryOpFormat {
    bool is_NoFormat { get; }
    bool is_CombineFormat { get; }
    _IUnaryOpFormat DowncastClone();
  }
  public abstract class UnaryOpFormat : _IUnaryOpFormat {
    public UnaryOpFormat() {
    }
    private static readonly DAST.Format._IUnaryOpFormat theDefault = create_NoFormat();
    public static DAST.Format._IUnaryOpFormat Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST.Format._IUnaryOpFormat> _TYPE = new Dafny.TypeDescriptor<DAST.Format._IUnaryOpFormat>(DAST.Format.UnaryOpFormat.Default());
    public static Dafny.TypeDescriptor<DAST.Format._IUnaryOpFormat> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUnaryOpFormat create_NoFormat() {
      return new UnaryOpFormat_NoFormat();
    }
    public static _IUnaryOpFormat create_CombineFormat() {
      return new UnaryOpFormat_CombineFormat();
    }
    public bool is_NoFormat { get { return this is UnaryOpFormat_NoFormat; } }
    public bool is_CombineFormat { get { return this is UnaryOpFormat_CombineFormat; } }
    public static System.Collections.Generic.IEnumerable<_IUnaryOpFormat> AllSingletonConstructors {
      get {
        yield return UnaryOpFormat.create_NoFormat();
        yield return UnaryOpFormat.create_CombineFormat();
      }
    }
    public abstract _IUnaryOpFormat DowncastClone();
  }
  public class UnaryOpFormat_NoFormat : UnaryOpFormat {
    public UnaryOpFormat_NoFormat() : base() {
    }
    public override _IUnaryOpFormat DowncastClone() {
      if (this is _IUnaryOpFormat dt) { return dt; }
      return new UnaryOpFormat_NoFormat();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Format.UnaryOpFormat_NoFormat;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Format.UnaryOpFormat.NoFormat";
      return s;
    }
  }
  public class UnaryOpFormat_CombineFormat : UnaryOpFormat {
    public UnaryOpFormat_CombineFormat() : base() {
    }
    public override _IUnaryOpFormat DowncastClone() {
      if (this is _IUnaryOpFormat dt) { return dt; }
      return new UnaryOpFormat_CombineFormat();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Format.UnaryOpFormat_CombineFormat;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Format.UnaryOpFormat.CombineFormat";
      return s;
    }
  }

  public interface _IBinaryOpFormat {
    bool is_NoFormat { get; }
    bool is_ImpliesFormat { get; }
    bool is_EquivalenceFormat { get; }
    bool is_ReverseFormat { get; }
    _IBinaryOpFormat DowncastClone();
  }
  public abstract class BinaryOpFormat : _IBinaryOpFormat {
    public BinaryOpFormat() {
    }
    private static readonly DAST.Format._IBinaryOpFormat theDefault = create_NoFormat();
    public static DAST.Format._IBinaryOpFormat Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST.Format._IBinaryOpFormat> _TYPE = new Dafny.TypeDescriptor<DAST.Format._IBinaryOpFormat>(DAST.Format.BinaryOpFormat.Default());
    public static Dafny.TypeDescriptor<DAST.Format._IBinaryOpFormat> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IBinaryOpFormat create_NoFormat() {
      return new BinaryOpFormat_NoFormat();
    }
    public static _IBinaryOpFormat create_ImpliesFormat() {
      return new BinaryOpFormat_ImpliesFormat();
    }
    public static _IBinaryOpFormat create_EquivalenceFormat() {
      return new BinaryOpFormat_EquivalenceFormat();
    }
    public static _IBinaryOpFormat create_ReverseFormat() {
      return new BinaryOpFormat_ReverseFormat();
    }
    public bool is_NoFormat { get { return this is BinaryOpFormat_NoFormat; } }
    public bool is_ImpliesFormat { get { return this is BinaryOpFormat_ImpliesFormat; } }
    public bool is_EquivalenceFormat { get { return this is BinaryOpFormat_EquivalenceFormat; } }
    public bool is_ReverseFormat { get { return this is BinaryOpFormat_ReverseFormat; } }
    public static System.Collections.Generic.IEnumerable<_IBinaryOpFormat> AllSingletonConstructors {
      get {
        yield return BinaryOpFormat.create_NoFormat();
        yield return BinaryOpFormat.create_ImpliesFormat();
        yield return BinaryOpFormat.create_EquivalenceFormat();
        yield return BinaryOpFormat.create_ReverseFormat();
      }
    }
    public abstract _IBinaryOpFormat DowncastClone();
  }
  public class BinaryOpFormat_NoFormat : BinaryOpFormat {
    public BinaryOpFormat_NoFormat() : base() {
    }
    public override _IBinaryOpFormat DowncastClone() {
      if (this is _IBinaryOpFormat dt) { return dt; }
      return new BinaryOpFormat_NoFormat();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Format.BinaryOpFormat_NoFormat;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Format.BinaryOpFormat.NoFormat";
      return s;
    }
  }
  public class BinaryOpFormat_ImpliesFormat : BinaryOpFormat {
    public BinaryOpFormat_ImpliesFormat() : base() {
    }
    public override _IBinaryOpFormat DowncastClone() {
      if (this is _IBinaryOpFormat dt) { return dt; }
      return new BinaryOpFormat_ImpliesFormat();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Format.BinaryOpFormat_ImpliesFormat;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Format.BinaryOpFormat.ImpliesFormat";
      return s;
    }
  }
  public class BinaryOpFormat_EquivalenceFormat : BinaryOpFormat {
    public BinaryOpFormat_EquivalenceFormat() : base() {
    }
    public override _IBinaryOpFormat DowncastClone() {
      if (this is _IBinaryOpFormat dt) { return dt; }
      return new BinaryOpFormat_EquivalenceFormat();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Format.BinaryOpFormat_EquivalenceFormat;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Format.BinaryOpFormat.EquivalenceFormat";
      return s;
    }
  }
  public class BinaryOpFormat_ReverseFormat : BinaryOpFormat {
    public BinaryOpFormat_ReverseFormat() : base() {
    }
    public override _IBinaryOpFormat DowncastClone() {
      if (this is _IBinaryOpFormat dt) { return dt; }
      return new BinaryOpFormat_ReverseFormat();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Format.BinaryOpFormat_ReverseFormat;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Format.BinaryOpFormat.ReverseFormat";
      return s;
    }
  }
} // end of namespace DAST.Format