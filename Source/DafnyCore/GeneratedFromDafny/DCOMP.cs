// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace DCOMP {

  public partial class __default {
    public static bool is__tuple__numeric(Dafny.ISequence<Dafny.Rune> i) {
      return ((((new BigInteger((i).Count)) >= (new BigInteger(2))) && (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_')))) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Contains((i).Select(BigInteger.One)))) && (((new BigInteger((i).Count)) == (new BigInteger(2))) || (((new BigInteger((i).Count)) == (new BigInteger(3))) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Contains((i).Select(new BigInteger(2))))));
    }
    public static bool has__special(Dafny.ISequence<Dafny.Rune> i) {
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return false;
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        return true;
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('#'))) {
        return true;
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        if ((new BigInteger(2)) <= (new BigInteger((i).Count))) {
          if (((i).Select(BigInteger.One)) != (new Dafny.Rune('_'))) {
            return true;
          } else {
            Dafny.ISequence<Dafny.Rune> _in113 = (i).Drop(new BigInteger(2));
            i = _in113;
            goto TAIL_CALL_START;
          }
        } else {
          return true;
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _in114 = (i).Drop(BigInteger.One);
        i = _in114;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> idiomatic__rust(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1696___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1696___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1696___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1696___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _1696___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1696___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1697___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1697___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1697___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1697___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _1697___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1697___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in118 = (i).Drop(BigInteger.One);
        i = _in118;
        goto TAIL_CALL_START;
      }
    }
    public static bool is__tuple__builder(Dafny.ISequence<Dafny.Rune> i) {
      return ((((new BigInteger((i).Count)) >= (new BigInteger(9))) && (((i).Take(new BigInteger(8))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("___hMake")))) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Contains((i).Select(new BigInteger(8))))) && (((new BigInteger((i).Count)) == (new BigInteger(9))) || (((new BigInteger((i).Count)) == (new BigInteger(10))) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Contains((i).Select(new BigInteger(9))))));
    }
    public static Dafny.ISequence<Dafny.Rune> better__tuple__builder__name(Dafny.ISequence<Dafny.Rune> i) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), (i).Drop(new BigInteger(8)));
    }
    public static bool is__dafny__generated__id(Dafny.ISequence<Dafny.Rune> i) {
      return ((((new BigInteger((i).Count)).Sign == 1) && (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_')))) && (!(DCOMP.__default.has__special((i).Drop(BigInteger.One))))) && (!((new BigInteger((i).Count)) >= (new BigInteger(2))) || (((i).Select(BigInteger.One)) != (new Dafny.Rune('T'))));
    }
    public static bool is__idiomatic__rust__id(Dafny.ISequence<Dafny.Rune> i) {
      return (((new BigInteger((i).Count)).Sign == 1) && (!(DCOMP.__default.has__special(i)))) && (!(DCOMP.__default.reserved__rust).Contains(i));
    }
    public static Dafny.ISequence<Dafny.Rune> escapeIdent(Dafny.ISequence<Dafny.Rune> i) {
      if (DCOMP.__default.is__tuple__numeric(i)) {
        return i;
      } else if (DCOMP.__default.is__tuple__builder(i)) {
        return DCOMP.__default.better__tuple__builder__name(i);
      } else if ((DCOMP.__default.reserved__rust).Contains(i)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), i);
      } else if (DCOMP.__default.is__idiomatic__rust__id(i)) {
        return DCOMP.__default.idiomatic__rust(i);
      } else if (DCOMP.__default.is__dafny__generated__id(i)) {
        return i;
      } else {
        Dafny.ISequence<Dafny.Rune> _1698_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1698_r);
      }
    }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("async"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("await"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("const"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("else"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("enum"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ref"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("static"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("struct"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("union"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Keywords"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abstract"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("become"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("box"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("do"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("final"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("macro"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("override"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("priv"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("try"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("typeof"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsized"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("virtual"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("yield"));
    } }
    public static Dafny.ISequence<Dafny.Rune> IND { get {
      return RAST.__default.IND;
    } }
  }

  public interface _IOwnership {
    bool is_OwnershipOwned { get; }
    bool is_OwnershipBorrowed { get; }
    bool is_OwnershipBorrowedMut { get; }
    bool is_OwnershipAutoBorrowed { get; }
    _IOwnership DowncastClone();
  }
  public abstract class Ownership : _IOwnership {
    public Ownership() {
    }
    private static readonly DCOMP._IOwnership theDefault = create_OwnershipOwned();
    public static DCOMP._IOwnership Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._IOwnership> _TYPE = new Dafny.TypeDescriptor<DCOMP._IOwnership>(DCOMP.Ownership.Default());
    public static Dafny.TypeDescriptor<DCOMP._IOwnership> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOwnership create_OwnershipOwned() {
      return new Ownership_OwnershipOwned();
    }
    public static _IOwnership create_OwnershipBorrowed() {
      return new Ownership_OwnershipBorrowed();
    }
    public static _IOwnership create_OwnershipBorrowedMut() {
      return new Ownership_OwnershipBorrowedMut();
    }
    public static _IOwnership create_OwnershipAutoBorrowed() {
      return new Ownership_OwnershipAutoBorrowed();
    }
    public bool is_OwnershipOwned { get { return this is Ownership_OwnershipOwned; } }
    public bool is_OwnershipBorrowed { get { return this is Ownership_OwnershipBorrowed; } }
    public bool is_OwnershipBorrowedMut { get { return this is Ownership_OwnershipBorrowedMut; } }
    public bool is_OwnershipAutoBorrowed { get { return this is Ownership_OwnershipAutoBorrowed; } }
    public static System.Collections.Generic.IEnumerable<_IOwnership> AllSingletonConstructors {
      get {
        yield return Ownership.create_OwnershipOwned();
        yield return Ownership.create_OwnershipBorrowed();
        yield return Ownership.create_OwnershipBorrowedMut();
        yield return Ownership.create_OwnershipAutoBorrowed();
      }
    }
    public abstract _IOwnership DowncastClone();
  }
  public class Ownership_OwnershipOwned : Ownership {
    public Ownership_OwnershipOwned() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipOwned();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Ownership_OwnershipOwned;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipOwned";
      return s;
    }
  }
  public class Ownership_OwnershipBorrowed : Ownership {
    public Ownership_OwnershipBorrowed() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipBorrowed();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Ownership_OwnershipBorrowed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipBorrowed";
      return s;
    }
  }
  public class Ownership_OwnershipBorrowedMut : Ownership {
    public Ownership_OwnershipBorrowedMut() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipBorrowedMut();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Ownership_OwnershipBorrowedMut;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipBorrowedMut";
      return s;
    }
  }
  public class Ownership_OwnershipAutoBorrowed : Ownership {
    public Ownership_OwnershipAutoBorrowed() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipAutoBorrowed();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Ownership_OwnershipAutoBorrowed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipAutoBorrowed";
      return s;
    }
  }

  public partial class COMP {
    public COMP() {
      this._UnicodeChars = false;
    }
    public void __ctor(bool UnicodeChars)
    {
      (this)._UnicodeChars = UnicodeChars;
    }
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<RAST._IModDecl> _1699_body;
      Dafny.ISequence<RAST._IModDecl> _out15;
      _out15 = (this).GenModuleBody((mod).dtor_body, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
      _1699_body = _out15;
      s = (((mod).dtor_isExtern) ? (RAST.Mod.create_ExternMod(DCOMP.__default.escapeIdent((mod).dtor_name))) : (RAST.Mod.create_Mod(DCOMP.__default.escapeIdent((mod).dtor_name), _1699_body)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _1700_i;
      _1700_i = BigInteger.Zero;
      while ((_1700_i) < (new BigInteger((body).Count))) {
        Dafny.ISequence<RAST._IModDecl> _1701_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source50 = (body).Select(_1700_i);
        if (_source50.is_Module) {
          DAST._IModule _1702___mcc_h0 = _source50.dtor_Module_a0;
          DAST._IModule _1703_m = _1702___mcc_h0;
          RAST._IMod _1704_mm;
          RAST._IMod _out16;
          _out16 = (this).GenModule(_1703_m, containingPath);
          _1704_mm = _out16;
          _1701_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1704_mm));
        } else if (_source50.is_Class) {
          DAST._IClass _1705___mcc_h1 = _source50.dtor_Class_a0;
          DAST._IClass _1706_c = _1705___mcc_h1;
          Dafny.ISequence<RAST._IModDecl> _out17;
          _out17 = (this).GenClass(_1706_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1706_c).dtor_name)));
          _1701_generated = _out17;
        } else if (_source50.is_Trait) {
          DAST._ITrait _1707___mcc_h2 = _source50.dtor_Trait_a0;
          DAST._ITrait _1708_t = _1707___mcc_h2;
          Dafny.ISequence<Dafny.Rune> _1709_tt;
          Dafny.ISequence<Dafny.Rune> _out18;
          _out18 = (this).GenTrait(_1708_t, containingPath);
          _1709_tt = _out18;
          _1701_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1709_tt));
        } else if (_source50.is_Newtype) {
          DAST._INewtype _1710___mcc_h3 = _source50.dtor_Newtype_a0;
          DAST._INewtype _1711_n = _1710___mcc_h3;
          Dafny.ISequence<RAST._IModDecl> _out19;
          _out19 = (this).GenNewtype(_1711_n);
          _1701_generated = _out19;
        } else {
          DAST._IDatatype _1712___mcc_h4 = _source50.dtor_Datatype_a0;
          DAST._IDatatype _1713_d = _1712___mcc_h4;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenDatatype(_1713_d);
          _1701_generated = _out20;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1701_generated);
        _1700_i = (_1700_i) + (BigInteger.One);
      }
      return s;
    }
    public void GenTypeParameters(Dafny.ISequence<DAST._IType> @params, out Dafny.ISet<DAST._IType> typeParamsSet, out Dafny.ISequence<RAST._ITypeParam> typeParams, out Dafny.ISequence<RAST._ITypeParam> constrainedTypeParams, out Dafny.ISequence<Dafny.Rune> whereConstraints)
    {
      typeParamsSet = Dafny.Set<DAST._IType>.Empty;
      typeParams = Dafny.Sequence<RAST._ITypeParam>.Empty;
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParam>.Empty;
      whereConstraints = Dafny.Sequence<Dafny.Rune>.Empty;
      typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      typeParams = Dafny.Sequence<RAST._ITypeParam>.FromElements();
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParam>.FromElements();
      whereConstraints = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _1714_tpI;
      _1714_tpI = BigInteger.Zero;
      if ((new BigInteger((@params).Count)).Sign == 1) {
        while ((_1714_tpI) < (new BigInteger((@params).Count))) {
          DAST._IType _1715_tp;
          _1715_tp = (@params).Select(_1714_tpI);
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1715_tp));
          RAST._IType _1716_genTp;
          RAST._IType _out21;
          _out21 = (this).GenType(_1715_tp, false, false);
          _1716_genTp = _out21;
          typeParams = Dafny.Sequence<RAST._ITypeParam>.Concat(typeParams, Dafny.Sequence<RAST._ITypeParam>.FromElements(RAST.TypeParam.create((_1716_genTp)._ToString(DCOMP.__default.IND), Dafny.Sequence<RAST._IType>.FromElements())));
          _1714_tpI = (_1714_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<RAST._IType> _1717_baseConstraints;
      _1717_baseConstraints = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.CloneTrait, RAST.__default.DafnyPrintTrait, RAST.__default.StaticTrait);
      constrainedTypeParams = RAST.TypeParam.AddConstraintsMultiple(typeParams, _1717_baseConstraints);
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1718_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1719_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1720_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1721_whereConstraints;
      Dafny.ISet<DAST._IType> _out22;
      Dafny.ISequence<RAST._ITypeParam> _out23;
      Dafny.ISequence<RAST._ITypeParam> _out24;
      Dafny.ISequence<Dafny.Rune> _out25;
      (this).GenTypeParameters((c).dtor_typeParams, out _out22, out _out23, out _out24, out _out25);
      _1718_typeParamsSet = _out22;
      _1719_sTypeParams = _out23;
      _1720_sConstrainedTypeParams = _out24;
      _1721_whereConstraints = _out25;
      Dafny.ISequence<Dafny.Rune> _1722_constrainedTypeParams;
      _1722_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1720_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IFormal> _1723_fields;
      _1723_fields = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1724_fieldInits;
      _1724_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _1725_fieldI;
      _1725_fieldI = BigInteger.Zero;
      while ((_1725_fieldI) < (new BigInteger(((c).dtor_fields).Count))) {
        DAST._IField _1726_field;
        _1726_field = ((c).dtor_fields).Select(_1725_fieldI);
        RAST._IType _1727_fieldType;
        RAST._IType _out26;
        _out26 = (this).GenType(((_1726_field).dtor_formal).dtor_typ, false, false);
        _1727_fieldType = _out26;
        _1723_fields = Dafny.Sequence<RAST._IFormal>.Concat(_1723_fields, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub "), DCOMP.__default.escapeIdent(((_1726_field).dtor_formal).dtor_name)), RAST.Type.create_TypeApp(RAST.__default.refcell__type, Dafny.Sequence<RAST._IType>.FromElements(_1727_fieldType)))));
        Std.Wrappers._IOption<DAST._IExpression> _source51 = (_1726_field).dtor_defaultValue;
        if (_source51.is_None) {
          {
            _1724_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1724_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(((_1726_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new(::std::default::Default::default())")))));
          }
        } else {
          DAST._IExpression _1728___mcc_h0 = _source51.dtor_value;
          DAST._IExpression _1729_e = _1728___mcc_h0;
          {
            RAST._IExpr _1730_eStr;
            DCOMP._IOwnership _1731___v30;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1732___v31;
            RAST._IExpr _out27;
            DCOMP._IOwnership _out28;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out29;
            (this).GenExpr(_1729_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out27, out _out28, out _out29);
            _1730_eStr = _out27;
            _1731___v30 = _out28;
            _1732___v31 = _out29;
            _1724_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1724_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(((_1726_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1730_eStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
          }
        }
        _1725_fieldI = (_1725_fieldI) + (BigInteger.One);
      }
      BigInteger _1733_typeParamI;
      _1733_typeParamI = BigInteger.Zero;
      while ((_1733_typeParamI) < (new BigInteger(((c).dtor_typeParams).Count))) {
        RAST._IType _1734_tpeGen;
        RAST._IType _out30;
        _out30 = (this).GenType(((c).dtor_typeParams).Select(_1733_typeParamI), false, false);
        _1734_tpeGen = _out30;
        _1723_fields = Dafny.Sequence<RAST._IFormal>.Concat(_1723_fields, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1733_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1734_tpeGen)))));
        _1724_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1724_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1733_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
        _1733_typeParamI = (_1733_typeParamI) + (BigInteger.One);
      }
      RAST._IStruct _1735_struct;
      _1735_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.__default.escapeIdent((c).dtor_name), _1719_sTypeParams, RAST.Formals.create_NamedFormals(_1723_fields));
      Dafny.ISequence<RAST._IType> _1736_typeParamsAsTypes;
      _1736_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1737_typeParam) => {
        return RAST.__default.RawType((_1737_typeParam).dtor_content);
      })), _1719_sTypeParams);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1735_struct));
      Dafny.ISequence<RAST._IImplMember> _1738_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1739_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out31;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out32;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(path)), _1718_typeParamsSet, out _out31, out _out32);
      _1738_implBodyRaw = _out31;
      _1739_traitBodies = _out32;
      Dafny.ISequence<RAST._IImplMember> _1740_implBody;
      _1740_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(DCOMP.__default.escapeIdent((c).dtor_name), _1724_fieldInits))))), _1738_implBodyRaw);
      RAST._IImpl _1741_i;
      _1741_i = RAST.Impl.create_Impl(_1720_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1736_typeParamsAsTypes), _1721_whereConstraints, _1740_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1741_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1742_i;
        _1742_i = BigInteger.Zero;
        while ((_1742_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1743_superClass;
          _1743_superClass = ((c).dtor_superClasses).Select(_1742_i);
          DAST._IType _source52 = _1743_superClass;
          if (_source52.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1744___mcc_h1 = _source52.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1745___mcc_h2 = _source52.dtor_typeArgs;
            DAST._IResolvedType _1746___mcc_h3 = _source52.dtor_resolved;
            DAST._IResolvedType _source53 = _1746___mcc_h3;
            if (_source53.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1747___mcc_h7 = _source53.dtor_path;
            } else if (_source53.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1748___mcc_h9 = _source53.dtor_path;
              Dafny.ISequence<DAST._IType> _1749_typeArgs = _1745___mcc_h2;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1750_traitPath = _1744___mcc_h1;
              {
                Dafny.ISequence<Dafny.Rune> _1751_pathStr;
                Dafny.ISequence<Dafny.Rune> _out33;
                _out33 = DCOMP.COMP.GenPath(_1750_traitPath);
                _1751_pathStr = _out33;
                Dafny.ISequence<RAST._IType> _1752_typeArgs;
                Dafny.ISequence<RAST._IType> _out34;
                _out34 = (this).GenTypeArgs(_1749_typeArgs, false, false);
                _1752_typeArgs = _out34;
                Dafny.ISequence<RAST._IImplMember> _1753_body;
                _1753_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1739_traitBodies).Contains(_1750_traitPath)) {
                  _1753_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1739_traitBodies,_1750_traitPath);
                }
                Dafny.ISequence<Dafny.Rune> _1754_genSelfPath;
                Dafny.ISequence<Dafny.Rune> _out35;
                _out35 = DCOMP.COMP.GenPath(path);
                _1754_genSelfPath = _out35;
                RAST._IModDecl _1755_x;
                _1755_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1720_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1751_pathStr), _1752_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1754_genSelfPath), _1736_typeParamsAsTypes)), _1721_whereConstraints, _1753_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1755_x));
              }
            } else {
              DAST._IType _1756___mcc_h11 = _source53.dtor_baseType;
              DAST._INewtypeRange _1757___mcc_h12 = _source53.dtor_range;
              bool _1758___mcc_h13 = _source53.dtor_erase;
            }
          } else if (_source52.is_Nullable) {
            DAST._IType _1759___mcc_h17 = _source52.dtor_Nullable_a0;
          } else if (_source52.is_Tuple) {
            Dafny.ISequence<DAST._IType> _1760___mcc_h19 = _source52.dtor_Tuple_a0;
          } else if (_source52.is_Array) {
            DAST._IType _1761___mcc_h21 = _source52.dtor_element;
            BigInteger _1762___mcc_h22 = _source52.dtor_dims;
          } else if (_source52.is_Seq) {
            DAST._IType _1763___mcc_h25 = _source52.dtor_element;
          } else if (_source52.is_Set) {
            DAST._IType _1764___mcc_h27 = _source52.dtor_element;
          } else if (_source52.is_Multiset) {
            DAST._IType _1765___mcc_h29 = _source52.dtor_element;
          } else if (_source52.is_Map) {
            DAST._IType _1766___mcc_h31 = _source52.dtor_key;
            DAST._IType _1767___mcc_h32 = _source52.dtor_value;
          } else if (_source52.is_SetBuilder) {
            DAST._IType _1768___mcc_h35 = _source52.dtor_element;
          } else if (_source52.is_MapBuilder) {
            DAST._IType _1769___mcc_h37 = _source52.dtor_key;
            DAST._IType _1770___mcc_h38 = _source52.dtor_value;
          } else if (_source52.is_Arrow) {
            Dafny.ISequence<DAST._IType> _1771___mcc_h41 = _source52.dtor_args;
            DAST._IType _1772___mcc_h42 = _source52.dtor_result;
          } else if (_source52.is_Primitive) {
            DAST._IPrimitive _1773___mcc_h45 = _source52.dtor_Primitive_a0;
          } else if (_source52.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1774___mcc_h47 = _source52.dtor_Passthrough_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _1775___mcc_h49 = _source52.dtor_TypeArg_a0;
          }
          _1742_i = (_1742_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1776_d;
      _1776_d = RAST.Impl.create_ImplFor(_1720_sConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1736_typeParamsAsTypes), _1721_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1777_defaultImpl;
      _1777_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1776_d));
      RAST._IImpl _1778_p;
      _1778_p = RAST.Impl.create_ImplFor(_1720_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1736_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), ((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1779_printImpl;
      _1779_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1778_p));
      RAST._IImpl _1780_pp;
      _1780_pp = RAST.Impl.create_ImplFor(_1719_sTypeParams, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1736_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.Self)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1781_ptrPartialEqImpl;
      _1781_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1780_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1777_defaultImpl), _1779_printImpl), _1781_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1782_typeParamsSet;
      _1782_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._IType> _1783_typeParams;
      _1783_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1784_tpI;
      _1784_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1784_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._IType _1785_tp;
          _1785_tp = ((t).dtor_typeParams).Select(_1784_tpI);
          _1782_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1782_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1785_tp));
          RAST._IType _1786_genTp;
          RAST._IType _out36;
          _out36 = (this).GenType(_1785_tp, false, false);
          _1786_genTp = _out36;
          _1783_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1783_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1786_genTp));
          _1784_tpI = (_1784_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1787_fullPath;
      _1787_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1788_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1789___v34;
      Dafny.ISequence<RAST._IImplMember> _out37;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out38;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1787_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1787_fullPath)), _1782_typeParamsSet, out _out37, out _out38);
      _1788_implBody = _out37;
      _1789___v34 = _out38;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(Dafny.Sequence<RAST._ITypeParam>.FromElements(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((t).dtor_name)), _1783_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1788_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1790_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1791_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1792_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1793_whereConstraints;
      Dafny.ISet<DAST._IType> _out39;
      Dafny.ISequence<RAST._ITypeParam> _out40;
      Dafny.ISequence<RAST._ITypeParam> _out41;
      Dafny.ISequence<Dafny.Rune> _out42;
      (this).GenTypeParameters((c).dtor_typeParams, out _out39, out _out40, out _out41, out _out42);
      _1790_typeParamsSet = _out39;
      _1791_sTypeParams = _out40;
      _1792_sConstrainedTypeParams = _out41;
      _1793_whereConstraints = _out42;
      Dafny.ISequence<RAST._IType> _1794_typeParamsAsTypes;
      _1794_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1795_t) => {
        return RAST.__default.RawType((_1795_t).dtor_content);
      })), _1791_sTypeParams);
      Dafny.ISequence<Dafny.Rune> _1796_constrainedTypeParams;
      _1796_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1792_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1797_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source54 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      if (_source54.is_None) {
        RAST._IType _out43;
        _out43 = (this).GenType((c).dtor_base, false, false);
        _1797_underlyingType = _out43;
      } else {
        RAST._IType _1798___mcc_h0 = _source54.dtor_value;
        RAST._IType _1799_v = _1798___mcc_h0;
        _1797_underlyingType = _1799_v;
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), DCOMP.__default.escapeIdent((c).dtor_name), _1791_sTypeParams, RAST.Formals.create_NamelessFormals(Dafny.Sequence<RAST._INamelessFormal>.FromElements(RAST.NamelessFormal.create(RAST.Visibility.create_PUB(), _1797_underlyingType))))));
      Dafny.ISequence<Dafny.Rune> _1800_fnBody;
      _1800_fnBody = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Std.Wrappers._IOption<DAST._IExpression> _source55 = (c).dtor_witnessExpr;
      if (_source55.is_None) {
        {
          _1800_fnBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1800_fnBody, DCOMP.__default.escapeIdent((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(::std::default::Default::default())"));
        }
      } else {
        DAST._IExpression _1801___mcc_h1 = _source55.dtor_value;
        DAST._IExpression _1802_e = _1801___mcc_h1;
        {
          RAST._IExpr _1803_eStr;
          DCOMP._IOwnership _1804___v35;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1805___v36;
          RAST._IExpr _out44;
          DCOMP._IOwnership _out45;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out46;
          (this).GenExpr(_1802_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out44, out _out45, out _out46);
          _1803_eStr = _out44;
          _1804___v35 = _out45;
          _1805___v36 = _out46;
          _1800_fnBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1800_fnBody, DCOMP.__default.escapeIdent((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1803_eStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
        }
      }
      RAST._IImplMember _1806_body;
      _1806_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(_1800_fnBody))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1792_sConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1794_typeParamsAsTypes), _1793_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1806_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1792_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1794_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1792_sConstrainedTypeParams, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1794_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1797_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&Self::Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1807_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1808_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1809_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1810_whereConstraints;
      Dafny.ISet<DAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParam> _out48;
      Dafny.ISequence<RAST._ITypeParam> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1807_typeParamsSet = _out47;
      _1808_sTypeParams = _out48;
      _1809_sConstrainedTypeParams = _out49;
      _1810_whereConstraints = _out50;
      Dafny.ISequence<RAST._IType> _1811_typeParamsAsTypes;
      _1811_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1812_t) => {
        return RAST.__default.RawType((_1812_t).dtor_content);
      })), _1808_sTypeParams);
      Dafny.ISequence<Dafny.Rune> _1813_constrainedTypeParams;
      _1813_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1809_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.IND, DCOMP.__default.IND));
      Dafny.ISequence<RAST._IEnumCase> _1814_ctors;
      _1814_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _1815_i;
      _1815_i = BigInteger.Zero;
      while ((_1815_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1816_ctor;
        _1816_ctor = ((c).dtor_ctors).Select(_1815_i);
        Dafny.ISequence<RAST._IFormal> _1817_ctorArgs;
        _1817_ctorArgs = Dafny.Sequence<RAST._IFormal>.FromElements();
        BigInteger _1818_j;
        _1818_j = BigInteger.Zero;
        while ((_1818_j) < (new BigInteger(((_1816_ctor).dtor_args).Count))) {
          DAST._IFormal _1819_formal;
          _1819_formal = ((_1816_ctor).dtor_args).Select(_1818_j);
          RAST._IType _1820_formalType;
          RAST._IType _out51;
          _out51 = (this).GenType((_1819_formal).dtor_typ, false, false);
          _1820_formalType = _out51;
          if ((c).dtor_isCo) {
            _1817_ctorArgs = Dafny.Sequence<RAST._IFormal>.Concat(_1817_ctorArgs, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1819_formal).dtor_name), RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1820_formalType)))));
          } else {
            _1817_ctorArgs = Dafny.Sequence<RAST._IFormal>.Concat(_1817_ctorArgs, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1819_formal).dtor_name), _1820_formalType)));
          }
          _1818_j = (_1818_j) + (BigInteger.One);
        }
        _1814_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1814_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeIdent((_1816_ctor).dtor_name), RAST.Formals.create_NamedFormals(_1817_ctorArgs))));
        _1815_i = (_1815_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1821_selfPath;
      _1821_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1822_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1823_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out52;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out53;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(_1821_selfPath)), _1807_typeParamsSet, out _out52, out _out53);
      _1822_implBodyRaw = _out52;
      _1823_traitBodies = _out53;
      Dafny.ISequence<RAST._IImplMember> _1824_implBody;
      _1824_implBody = _1822_implBodyRaw;
      _1815_i = BigInteger.Zero;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1825_emittedFields;
      _1825_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      while ((_1815_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1826_ctor;
        _1826_ctor = ((c).dtor_ctors).Select(_1815_i);
        BigInteger _1827_j;
        _1827_j = BigInteger.Zero;
        while ((_1827_j) < (new BigInteger(((_1826_ctor).dtor_args).Count))) {
          DAST._IFormal _1828_formal;
          _1828_formal = ((_1826_ctor).dtor_args).Select(_1827_j);
          if (!((_1825_emittedFields).Contains((_1828_formal).dtor_name))) {
            _1825_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1825_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1828_formal).dtor_name));
            RAST._IType _1829_formalType;
            RAST._IType _out54;
            _out54 = (this).GenType((_1828_formal).dtor_typ, false, false);
            _1829_formalType = _out54;
            Dafny.ISequence<RAST._IMatchCase> _1830_cases;
            _1830_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _1831_k;
            _1831_k = BigInteger.Zero;
            while ((_1831_k) < (new BigInteger(((c).dtor_ctors).Count))) {
              DAST._IDatatypeCtor _1832_ctor2;
              _1832_ctor2 = ((c).dtor_ctors).Select(_1831_k);
              Dafny.ISequence<Dafny.Rune> _1833_pattern;
              _1833_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent((_1832_ctor2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              Dafny.ISequence<Dafny.Rune> _1834_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              BigInteger _1835_l;
              _1835_l = BigInteger.Zero;
              bool _1836_hasMatchingField;
              _1836_hasMatchingField = false;
              while ((_1835_l) < (new BigInteger(((_1832_ctor2).dtor_args).Count))) {
                DAST._IFormal _1837_formal2;
                _1837_formal2 = ((_1832_ctor2).dtor_args).Select(_1835_l);
                if (((_1828_formal).dtor_name).Equals((_1837_formal2).dtor_name)) {
                  _1836_hasMatchingField = true;
                }
                _1833_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1833_pattern, DCOMP.__default.escapeIdent((_1837_formal2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _1835_l = (_1835_l) + (BigInteger.One);
              }
              _1833_pattern = Dafny.Sequence<Dafny.Rune>.Concat(_1833_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              if (_1836_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _1834_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), DCOMP.__default.escapeIdent((_1828_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1834_rhs = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((_1828_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1834_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1838_ctorMatch;
              _1838_ctorMatch = RAST.MatchCase.create(_1833_pattern, RAST.Expr.create_RawExpr(_1834_rhs));
              _1830_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1830_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1838_ctorMatch));
              _1831_k = (_1831_k) + (BigInteger.One);
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1830_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1830_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1839_methodBody;
            _1839_methodBody = RAST.Expr.create_Match(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")), _1830_cases);
            _1824_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1824_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(DCOMP.__default.escapeIdent((_1828_formal).dtor_name), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1829_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1839_methodBody)))));
          }
          _1827_j = (_1827_j) + (BigInteger.One);
        }
        _1815_i = (_1815_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _1840_typeI;
        _1840_typeI = BigInteger.Zero;
        Dafny.ISequence<RAST._IType> _1841_types;
        _1841_types = Dafny.Sequence<RAST._IType>.FromElements();
        while ((_1840_typeI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          RAST._IType _1842_genTp;
          RAST._IType _out55;
          _out55 = (this).GenType(((c).dtor_typeParams).Select(_1840_typeI), false, false);
          _1842_genTp = _out55;
          _1841_types = Dafny.Sequence<RAST._IType>.Concat(_1841_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData::")), Dafny.Sequence<RAST._IType>.FromElements(_1842_genTp))));
          _1840_typeI = (_1840_typeI) + (BigInteger.One);
        }
        _1814_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1814_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Formals.create_NamelessFormals(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessFormal>(((System.Func<RAST._IType, RAST._INamelessFormal>)((_1843_tpe) => {
  return RAST.NamelessFormal.create(RAST.Visibility.create_PRIV(), _1843_tpe);
})), _1841_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1844_enumBody;
      _1844_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq)]")), DCOMP.__default.escapeIdent((c).dtor_name), _1808_sTypeParams, _1814_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1809_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1811_typeParamsAsTypes), _1810_whereConstraints, _1824_implBody)));
      _1815_i = BigInteger.Zero;
      Dafny.ISequence<RAST._IMatchCase> _1845_printImplBodyCases;
      _1845_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      while ((_1815_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1846_ctor;
        _1846_ctor = ((c).dtor_ctors).Select(_1815_i);
        Dafny.ISequence<Dafny.Rune> _1847_ctorMatch;
        _1847_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((_1846_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _1848_modulePrefix;
        _1848_modulePrefix = (((((c).dtor_enclosingModule)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(((c).dtor_enclosingModule), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        RAST._IExpr _1849_printRhs;
        _1849_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1848_modulePrefix), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent((_1846_ctor).dtor_name)), (((_1846_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        BigInteger _1850_j;
        _1850_j = BigInteger.Zero;
        while ((_1850_j) < (new BigInteger(((_1846_ctor).dtor_args).Count))) {
          DAST._IFormal _1851_formal;
          _1851_formal = ((_1846_ctor).dtor_args).Select(_1850_j);
          _1847_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1847_ctorMatch, DCOMP.__default.escapeIdent((_1851_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1850_j).Sign == 1) {
            _1849_printRhs = (_1849_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1849_printRhs = (_1849_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), DCOMP.__default.escapeIdent((_1851_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
          _1850_j = (_1850_j) + (BigInteger.One);
        }
        _1847_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_1847_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_1846_ctor).dtor_hasAnyArgs) {
          _1849_printRhs = (_1849_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1849_printRhs = (_1849_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1845_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1845_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1847_ctorMatch), RAST.Expr.create_Block(_1849_printRhs))));
        _1815_i = (_1815_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1845_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1845_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      RAST._IExpr _1852_printImplBody;
      _1852_printImplBody = RAST.Expr.create_Match(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")), _1845_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1853_printImpl;
      _1853_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1809_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1811_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1852_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1854_defaultImpl;
      _1854_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        _1815_i = BigInteger.Zero;
        Dafny.ISequence<Dafny.Rune> _1855_structName;
        _1855_structName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1856_structAssignments;
        _1856_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        while ((_1815_i) < (new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count))) {
          DAST._IFormal _1857_formal;
          _1857_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1815_i);
          _1856_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1856_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent((_1857_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
          _1815_i = (_1815_i) + (BigInteger.One);
        }
        Dafny.ISequence<RAST._ITypeParam> _1858_defaultConstrainedTypeParams;
        _1858_defaultConstrainedTypeParams = RAST.TypeParam.AddConstraintsMultiple(_1808_sTypeParams, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        _1854_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1858_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1811_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1855_structName, _1856_structAssignments))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1844_enumBody, _1853_printImpl), _1854_defaultImpl);
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((new BigInteger((p).Count)).Sign == 0) {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
        return s;
      } else {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super::");
        BigInteger _1859_i;
        _1859_i = BigInteger.Zero;
        while ((_1859_i) < (new BigInteger((p).Count))) {
          if ((_1859_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeIdent(((p).Select(_1859_i))));
          _1859_i = (_1859_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1860_i;
        _1860_i = BigInteger.Zero;
        while ((_1860_i) < (new BigInteger((args).Count))) {
          RAST._IType _1861_genTp;
          RAST._IType _out56;
          _out56 = (this).GenType((args).Select(_1860_i), inBinding, inFn);
          _1861_genTp = _out56;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1861_genTp));
          _1860_i = (_1860_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public RAST._IType GenType(DAST._IType c, bool inBinding, bool inFn)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source56 = c;
      if (_source56.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1862___mcc_h0 = _source56.dtor_Path_a0;
        Dafny.ISequence<DAST._IType> _1863___mcc_h1 = _source56.dtor_typeArgs;
        DAST._IResolvedType _1864___mcc_h2 = _source56.dtor_resolved;
        DAST._IResolvedType _1865_resolved = _1864___mcc_h2;
        Dafny.ISequence<DAST._IType> _1866_args = _1863___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1867_p = _1862___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _1868_t;
          Dafny.ISequence<Dafny.Rune> _out57;
          _out57 = DCOMP.COMP.GenPath(_1867_p);
          _1868_t = _out57;
          s = RAST.Type.create_TIdentifier(_1868_t);
          Dafny.ISequence<RAST._IType> _1869_typeArgs;
          Dafny.ISequence<RAST._IType> _out58;
          _out58 = (this).GenTypeArgs(_1866_args, inBinding, inFn);
          _1869_typeArgs = _out58;
          s = RAST.Type.create_TypeApp(s, _1869_typeArgs);
          DAST._IResolvedType _source57 = _1865_resolved;
          if (_source57.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1870___mcc_h21 = _source57.dtor_path;
            {
              s = RAST.__default.Rc(s);
            }
          } else if (_source57.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1871___mcc_h22 = _source57.dtor_path;
            {
              if ((_1867_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<dyn ::std::any::Any>"));
              } else {
                if (inBinding) {
                  s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
                } else {
                  s = RAST.Type.create_ImplType(s);
                }
              }
            }
          } else {
            DAST._IType _1872___mcc_h23 = _source57.dtor_baseType;
            DAST._INewtypeRange _1873___mcc_h24 = _source57.dtor_range;
            bool _1874___mcc_h25 = _source57.dtor_erase;
            bool _1875_erased = _1874___mcc_h25;
            DAST._INewtypeRange _1876_range = _1873___mcc_h24;
            DAST._IType _1877_t = _1872___mcc_h23;
            {
              if (_1875_erased) {
                Std.Wrappers._IOption<RAST._IType> _source58 = DCOMP.COMP.NewtypeToRustType(_1877_t, _1876_range);
                if (_source58.is_None) {
                } else {
                  RAST._IType _1878___mcc_h26 = _source58.dtor_value;
                  RAST._IType _1879_v = _1878___mcc_h26;
                  s = _1879_v;
                }
              }
            }
          }
        }
      } else if (_source56.is_Nullable) {
        DAST._IType _1880___mcc_h3 = _source56.dtor_Nullable_a0;
        DAST._IType _1881_inner = _1880___mcc_h3;
        {
          RAST._IType _1882_innerExpr;
          RAST._IType _out59;
          _out59 = (this).GenType(_1881_inner, inBinding, inFn);
          _1882_innerExpr = _out59;
          s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1882_innerExpr));
        }
      } else if (_source56.is_Tuple) {
        Dafny.ISequence<DAST._IType> _1883___mcc_h4 = _source56.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IType> _1884_types = _1883___mcc_h4;
        {
          Dafny.ISequence<RAST._IType> _1885_args;
          _1885_args = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _1886_i;
          _1886_i = BigInteger.Zero;
          while ((_1886_i) < (new BigInteger((_1884_types).Count))) {
            RAST._IType _1887_generated;
            RAST._IType _out60;
            _out60 = (this).GenType((_1884_types).Select(_1886_i), inBinding, inFn);
            _1887_generated = _out60;
            _1885_args = Dafny.Sequence<RAST._IType>.Concat(_1885_args, Dafny.Sequence<RAST._IType>.FromElements(_1887_generated));
            _1886_i = (_1886_i) + (BigInteger.One);
          }
          s = RAST.Type.create_TupleType(_1885_args);
        }
      } else if (_source56.is_Array) {
        DAST._IType _1888___mcc_h5 = _source56.dtor_element;
        BigInteger _1889___mcc_h6 = _source56.dtor_dims;
        BigInteger _1890_dims = _1889___mcc_h6;
        DAST._IType _1891_element = _1888___mcc_h5;
        {
          RAST._IType _1892_elem;
          RAST._IType _out61;
          _out61 = (this).GenType(_1891_element, inBinding, inFn);
          _1892_elem = _out61;
          s = _1892_elem;
          BigInteger _1893_i;
          _1893_i = BigInteger.Zero;
          while ((_1893_i) < (_1890_dims)) {
            s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
            _1893_i = (_1893_i) + (BigInteger.One);
          }
        }
      } else if (_source56.is_Seq) {
        DAST._IType _1894___mcc_h7 = _source56.dtor_element;
        DAST._IType _1895_element = _1894___mcc_h7;
        {
          RAST._IType _1896_elem;
          RAST._IType _out62;
          _out62 = (this).GenType(_1895_element, inBinding, inFn);
          _1896_elem = _out62;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1896_elem));
        }
      } else if (_source56.is_Set) {
        DAST._IType _1897___mcc_h8 = _source56.dtor_element;
        DAST._IType _1898_element = _1897___mcc_h8;
        {
          RAST._IType _1899_elem;
          RAST._IType _out63;
          _out63 = (this).GenType(_1898_element, inBinding, inFn);
          _1899_elem = _out63;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1899_elem));
        }
      } else if (_source56.is_Multiset) {
        DAST._IType _1900___mcc_h9 = _source56.dtor_element;
        DAST._IType _1901_element = _1900___mcc_h9;
        {
          RAST._IType _1902_elem;
          RAST._IType _out64;
          _out64 = (this).GenType(_1901_element, inBinding, inFn);
          _1902_elem = _out64;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1902_elem));
        }
      } else if (_source56.is_Map) {
        DAST._IType _1903___mcc_h10 = _source56.dtor_key;
        DAST._IType _1904___mcc_h11 = _source56.dtor_value;
        DAST._IType _1905_value = _1904___mcc_h11;
        DAST._IType _1906_key = _1903___mcc_h10;
        {
          RAST._IType _1907_keyType;
          RAST._IType _out65;
          _out65 = (this).GenType(_1906_key, inBinding, inFn);
          _1907_keyType = _out65;
          RAST._IType _1908_valueType;
          RAST._IType _out66;
          _out66 = (this).GenType(_1905_value, inBinding, inFn);
          _1908_valueType = _out66;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1907_keyType, _1908_valueType));
        }
      } else if (_source56.is_SetBuilder) {
        DAST._IType _1909___mcc_h12 = _source56.dtor_element;
        DAST._IType _1910_elem = _1909___mcc_h12;
        {
          RAST._IType _1911_elemType;
          RAST._IType _out67;
          _out67 = (this).GenType(_1910_elem, inBinding, inFn);
          _1911_elemType = _out67;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1911_elemType));
        }
      } else if (_source56.is_MapBuilder) {
        DAST._IType _1912___mcc_h13 = _source56.dtor_key;
        DAST._IType _1913___mcc_h14 = _source56.dtor_value;
        DAST._IType _1914_value = _1913___mcc_h14;
        DAST._IType _1915_key = _1912___mcc_h13;
        {
          RAST._IType _1916_keyType;
          RAST._IType _out68;
          _out68 = (this).GenType(_1915_key, inBinding, inFn);
          _1916_keyType = _out68;
          RAST._IType _1917_valueType;
          RAST._IType _out69;
          _out69 = (this).GenType(_1914_value, inBinding, inFn);
          _1917_valueType = _out69;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1916_keyType, _1917_valueType));
        }
      } else if (_source56.is_Arrow) {
        Dafny.ISequence<DAST._IType> _1918___mcc_h15 = _source56.dtor_args;
        DAST._IType _1919___mcc_h16 = _source56.dtor_result;
        DAST._IType _1920_result = _1919___mcc_h16;
        Dafny.ISequence<DAST._IType> _1921_args = _1918___mcc_h15;
        {
          Dafny.ISequence<RAST._IType> _1922_argTypes;
          _1922_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _1923_i;
          _1923_i = BigInteger.Zero;
          while ((_1923_i) < (new BigInteger((_1921_args).Count))) {
            RAST._IType _1924_generated;
            RAST._IType _out70;
            _out70 = (this).GenType((_1921_args).Select(_1923_i), inBinding, true);
            _1924_generated = _out70;
            _1922_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1922_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1924_generated)));
            _1923_i = (_1923_i) + (BigInteger.One);
          }
          RAST._IType _1925_resultType;
          RAST._IType _out71;
          _out71 = (this).GenType(_1920_result, inBinding, (inFn) || (inBinding));
          _1925_resultType = _out71;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("FunctionWrapper")), Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_FnType(_1922_argTypes, RAST.Type.create_IntersectionType(_1925_resultType, RAST.__default.StaticTrait))));
        }
      } else if (_source56.is_Primitive) {
        DAST._IPrimitive _1926___mcc_h17 = _source56.dtor_Primitive_a0;
        DAST._IPrimitive _1927_p = _1926___mcc_h17;
        {
          DAST._IPrimitive _source59 = _1927_p;
          if (_source59.is_Int) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
          } else if (_source59.is_Real) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
          } else if (_source59.is_String) {
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
          } else if (_source59.is_Bool) {
            s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool"));
          } else {
            s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
          }
        }
      } else if (_source56.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _1928___mcc_h18 = _source56.dtor_Passthrough_a0;
        Dafny.ISequence<Dafny.Rune> _1929_v = _1928___mcc_h18;
        s = RAST.__default.RawType(_1929_v);
      } else {
        Dafny.ISequence<Dafny.Rune> _1930___mcc_h19 = _source56.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _source60 = _1930___mcc_h19;
        Dafny.ISequence<Dafny.Rune> _1931___mcc_h20 = _source60;
        Dafny.ISequence<Dafny.Rune> _1932_name = _1931___mcc_h20;
        s = RAST.__default.RawType(DCOMP.__default.escapeIdent(_1932_name));
      }
      return s;
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _1933_i;
      _1933_i = BigInteger.Zero;
      while ((_1933_i) < (new BigInteger((body).Count))) {
        DAST._IMethod _source61 = (body).Select(_1933_i);
        DAST._IMethod _1934___mcc_h0 = _source61;
        DAST._IMethod _1935_m = _1934___mcc_h0;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source62 = (_1935_m).dtor_overridingPath;
          if (_source62.is_None) {
            {
              RAST._IImplMember _1936_generated;
              RAST._IImplMember _out72;
              _out72 = (this).GenMethod(_1935_m, forTrait, enclosingType, enclosingTypeParams);
              _1936_generated = _out72;
              s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1936_generated));
            }
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1937___mcc_h1 = _source62.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1938_p = _1937___mcc_h1;
            {
              Dafny.ISequence<RAST._IImplMember> _1939_existing;
              _1939_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
              if ((traitBodies).Contains(_1938_p)) {
                _1939_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1938_p);
              }
              RAST._IImplMember _1940_genMethod;
              RAST._IImplMember _out73;
              _out73 = (this).GenMethod(_1935_m, true, enclosingType, enclosingTypeParams);
              _1940_genMethod = _out73;
              _1939_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1939_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1940_genMethod));
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1938_p, _1939_existing)));
            }
          }
        }
        _1933_i = (_1933_i) + (BigInteger.One);
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _1941_i;
      _1941_i = BigInteger.Zero;
      while ((_1941_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _1942_param;
        _1942_param = (@params).Select(_1941_i);
        RAST._IType _1943_paramType;
        RAST._IType _out74;
        _out74 = (this).GenType((_1942_param).dtor_typ, false, false);
        _1943_paramType = _out74;
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1942_param).dtor_name), RAST.Type.create_Borrowed(_1943_paramType))));
        _1941_i = (_1941_i) + (BigInteger.One);
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1944_params;
      Dafny.ISequence<RAST._IFormal> _out75;
      _out75 = (this).GenParams((m).dtor_params);
      _1944_params = _out75;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1945_paramNames;
      _1945_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1946_paramI;
      _1946_paramI = BigInteger.Zero;
      while ((_1946_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _1945_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1945_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_1946_paramI)).dtor_name));
        _1946_paramI = (_1946_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _1944_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), _1944_params);
        } else {
          RAST._IType _1947_tpe;
          RAST._IType _out76;
          _out76 = (this).GenType(enclosingType, false, false);
          _1947_tpe = _out76;
          _1944_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.Type.create_Borrowed(_1947_tpe))), _1944_params);
        }
      }
      Dafny.ISequence<RAST._IType> _1948_retTypeArgs;
      _1948_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1949_typeI;
      _1949_typeI = BigInteger.Zero;
      while ((_1949_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1950_typeExpr;
        RAST._IType _out77;
        _out77 = (this).GenType(((m).dtor_outTypes).Select(_1949_typeI), false, false);
        _1950_typeExpr = _out77;
        _1948_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1948_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1950_typeExpr));
        _1949_typeI = (_1949_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1951_visibility;
      _1951_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<Dafny.Rune> _1952_fnName;
      _1952_fnName = DCOMP.__default.escapeIdent((m).dtor_name);
      Dafny.ISequence<DAST._IType> _1953_typeParamsFiltered;
      _1953_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _1954_typeParamI;
      _1954_typeParamI = BigInteger.Zero;
      while ((_1954_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _1955_typeParam;
        _1955_typeParam = ((m).dtor_typeParams).Select(_1954_typeParamI);
        if (!((enclosingTypeParams).Contains(_1955_typeParam))) {
          _1953_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_1953_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_1955_typeParam));
        }
        _1954_typeParamI = (_1954_typeParamI) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.Rune> _1956_whereClauses;
      _1956_whereClauses = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Dafny.ISequence<RAST._ITypeParam> _1957_typeParams;
      _1957_typeParams = Dafny.Sequence<RAST._ITypeParam>.FromElements();
      if ((new BigInteger((_1953_typeParamsFiltered).Count)).Sign == 1) {
        _1956_whereClauses = Dafny.Sequence<Dafny.Rune>.Concat(_1956_whereClauses, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" where "));
        BigInteger _1958_i;
        _1958_i = BigInteger.Zero;
        while ((_1958_i) < (new BigInteger((_1953_typeParamsFiltered).Count))) {
          RAST._IType _1959_typeExpr;
          RAST._IType _out78;
          _out78 = (this).GenType((_1953_typeParamsFiltered).Select(_1958_i), false, false);
          _1959_typeExpr = _out78;
          _1957_typeParams = Dafny.Sequence<RAST._ITypeParam>.Concat(_1957_typeParams, Dafny.Sequence<RAST._ITypeParam>.FromElements(RAST.TypeParam.create((_1959_typeExpr)._ToString(DCOMP.__default.IND), Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.CloneTrait, RAST.__default.DafnyPrintTrait, RAST.__default.DefaultTrait, RAST.__default.StaticTrait))));
          _1958_i = (_1958_i) + (BigInteger.One);
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1960_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1961_earlyReturn;
        _1961_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source63 = (m).dtor_outVars;
        if (_source63.is_None) {
        } else {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1962___mcc_h0 = _source63.dtor_value;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1963_outVars = _1962___mcc_h0;
          {
            Dafny.ISequence<RAST._IExpr> _1964_tupleArgs;
            _1964_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _1965_outI;
            _1965_outI = BigInteger.Zero;
            while ((_1965_outI) < (new BigInteger((_1963_outVars).Count))) {
              Dafny.ISequence<Dafny.Rune> _1966_outVar;
              _1966_outVar = (_1963_outVars).Select(_1965_outI);
              _1964_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1964_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent((_1966_outVar)))));
              _1965_outI = (_1965_outI) + (BigInteger.One);
            }
            _1961_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1964_tupleArgs)));
          }
        }
        RAST._IExpr _1967_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1968___v39;
        RAST._IExpr _out79;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out80;
        (this).GenStmts((m).dtor_body, (((m).dtor_isStatic) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))), _1945_paramNames, true, _1961_earlyReturn, out _out79, out _out80);
        _1967_body = _out79;
        _1968___v39 = _out80;
        _1960_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some(_1967_body);
      } else {
        _1960_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1951_visibility, RAST.Fn.create(_1952_fnName, _1957_typeParams, _1944_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1948_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1948_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1948_retTypeArgs)))), _1956_whereClauses, _1960_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1969_declarations;
      _1969_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1970_i;
      _1970_i = BigInteger.Zero;
      while ((_1970_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _1971_stmt;
        _1971_stmt = (stmts).Select(_1970_i);
        RAST._IExpr _1972_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1973_recIdents;
        RAST._IExpr _out81;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out82;
        (this).GenStmt(_1971_stmt, selfIdent, @params, (isLast) && ((_1970_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out81, out _out82);
        _1972_stmtExpr = _out81;
        _1973_recIdents = _out82;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1973_recIdents, _1969_declarations));
        DAST._IStatement _source64 = _1971_stmt;
        if (_source64.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1974___mcc_h0 = _source64.dtor_name;
          DAST._IType _1975___mcc_h1 = _source64.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> _1976___mcc_h2 = _source64.dtor_maybeValue;
          Dafny.ISequence<Dafny.Rune> _1977_name = _1974___mcc_h0;
          {
            _1969_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1969_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1977_name));
          }
        } else if (_source64.is_Assign) {
          DAST._IAssignLhs _1978___mcc_h6 = _source64.dtor_lhs;
          DAST._IExpression _1979___mcc_h7 = _source64.dtor_value;
        } else if (_source64.is_If) {
          DAST._IExpression _1980___mcc_h10 = _source64.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1981___mcc_h11 = _source64.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1982___mcc_h12 = _source64.dtor_els;
        } else if (_source64.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1983___mcc_h16 = _source64.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1984___mcc_h17 = _source64.dtor_body;
        } else if (_source64.is_While) {
          DAST._IExpression _1985___mcc_h20 = _source64.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1986___mcc_h21 = _source64.dtor_body;
        } else if (_source64.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1987___mcc_h24 = _source64.dtor_boundName;
          DAST._IType _1988___mcc_h25 = _source64.dtor_boundType;
          DAST._IExpression _1989___mcc_h26 = _source64.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1990___mcc_h27 = _source64.dtor_body;
        } else if (_source64.is_Call) {
          DAST._IExpression _1991___mcc_h32 = _source64.dtor_on;
          DAST._ICallName _1992___mcc_h33 = _source64.dtor_callName;
          Dafny.ISequence<DAST._IType> _1993___mcc_h34 = _source64.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1994___mcc_h35 = _source64.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1995___mcc_h36 = _source64.dtor_outs;
        } else if (_source64.is_Return) {
          DAST._IExpression _1996___mcc_h42 = _source64.dtor_expr;
        } else if (_source64.is_EarlyReturn) {
        } else if (_source64.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1997___mcc_h44 = _source64.dtor_toLabel;
        } else if (_source64.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1998___mcc_h46 = _source64.dtor_body;
        } else if (_source64.is_JumpTailCallStart) {
        } else if (_source64.is_Halt) {
        } else {
          DAST._IExpression _1999___mcc_h48 = _source64.dtor_Print_a0;
        }
        generated = (generated).Then(_1972_stmtExpr);
        _1970_i = (_1970_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, Dafny.ISequence<Dafny.Rune> rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, out Dafny.ISequence<Dafny.Rune> generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IAssignLhs _source65 = lhs;
      if (_source65.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _2000___mcc_h0 = _source65.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _source66 = _2000___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _2001___mcc_h1 = _source66;
        Dafny.ISequence<Dafny.Rune> _2002_id = _2001___mcc_h1;
        {
          if ((@params).Contains(_2002_id)) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), DCOMP.__default.escapeIdent(_2002_id));
          } else {
            generated = DCOMP.__default.escapeIdent(_2002_id);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2002_id);
          needsIIFE = false;
        }
      } else if (_source65.is_Select) {
        DAST._IExpression _2003___mcc_h2 = _source65.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2004___mcc_h3 = _source65.dtor_field;
        Dafny.ISequence<Dafny.Rune> _2005_field = _2004___mcc_h3;
        DAST._IExpression _2006_on = _2003___mcc_h2;
        {
          RAST._IExpr _2007_onExpr;
          DCOMP._IOwnership _2008_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2009_recIdents;
          RAST._IExpr _out83;
          DCOMP._IOwnership _out84;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out85;
          (this).GenExpr(_2006_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out83, out _out84, out _out85);
          _2007_onExpr = _out83;
          _2008_onOwned = _out84;
          _2009_recIdents = _out85;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_2007_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _2005_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          readIdents = _2009_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _2010___mcc_h4 = _source65.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2011___mcc_h5 = _source65.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2012_indices = _2011___mcc_h5;
        DAST._IExpression _2013_on = _2010___mcc_h4;
        {
          RAST._IExpr _2014_onExpr;
          DCOMP._IOwnership _2015_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2016_recIdents;
          RAST._IExpr _out86;
          DCOMP._IOwnership _out87;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out88;
          (this).GenExpr(_2013_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out86, out _out87, out _out88);
          _2014_onExpr = _out86;
          _2015_onOwned = _out87;
          _2016_recIdents = _out88;
          readIdents = _2016_recIdents;
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _2017_i;
          _2017_i = BigInteger.Zero;
          while ((_2017_i) < (new BigInteger((_2012_indices).Count))) {
            RAST._IExpr _2018_idx;
            DCOMP._IOwnership _2019___v43;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2020_recIdentsIdx;
            RAST._IExpr _out89;
            DCOMP._IOwnership _out90;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
            (this).GenExpr((_2012_indices).Select(_2017_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out89, out _out90, out _out91);
            _2018_idx = _out89;
            _2019___v43 = _out90;
            _2020_recIdentsIdx = _out91;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_2017_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_2018_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2020_recIdentsIdx);
            _2017_i = (_2017_i) + (BigInteger.One);
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, (_2014_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _2017_i = BigInteger.Zero;
          while ((_2017_i) < (new BigInteger((_2012_indices).Count))) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_2017_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _2017_i = (_2017_i) + (BigInteger.One);
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}"));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IStatement _source67 = stmt;
      if (_source67.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _2021___mcc_h0 = _source67.dtor_name;
        DAST._IType _2022___mcc_h1 = _source67.dtor_typ;
        Std.Wrappers._IOption<DAST._IExpression> _2023___mcc_h2 = _source67.dtor_maybeValue;
        Std.Wrappers._IOption<DAST._IExpression> _source68 = _2023___mcc_h2;
        if (_source68.is_None) {
          DAST._IType _2024_typ = _2022___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2025_name = _2021___mcc_h0;
          {
            RAST._IType _2026_typeString;
            RAST._IType _out92;
            _out92 = (this).GenType(_2024_typ, true, false);
            _2026_typeString = _out92;
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_2025_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2026_typeString), Std.Wrappers.Option<RAST._IExpr>.create_None());
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else {
          DAST._IExpression _2027___mcc_h3 = _source68.dtor_value;
          DAST._IExpression _2028_expression = _2027___mcc_h3;
          DAST._IType _2029_typ = _2022___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2030_name = _2021___mcc_h0;
          {
            RAST._IType _2031_typeString;
            RAST._IType _out93;
            _out93 = (this).GenType(_2029_typ, true, false);
            _2031_typeString = _out93;
            RAST._IExpr _2032_expr;
            DCOMP._IOwnership _2033___v44;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2034_recIdents;
            RAST._IExpr _out94;
            DCOMP._IOwnership _out95;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
            (this).GenExpr(_2028_expression, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out94, out _out95, out _out96);
            _2032_expr = _out94;
            _2033___v44 = _out95;
            _2034_recIdents = _out96;
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_2030_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2031_typeString), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2032_expr));
            readIdents = _2034_recIdents;
          }
        }
      } else if (_source67.is_Assign) {
        DAST._IAssignLhs _2035___mcc_h4 = _source67.dtor_lhs;
        DAST._IExpression _2036___mcc_h5 = _source67.dtor_value;
        DAST._IExpression _2037_expression = _2036___mcc_h5;
        DAST._IAssignLhs _2038_lhs = _2035___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _2039_lhsGen;
          bool _2040_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2041_recIdents;
          Dafny.ISequence<Dafny.Rune> _out97;
          bool _out98;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out99;
          (this).GenAssignLhs(_2038_lhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), selfIdent, @params, out _out97, out _out98, out _out99);
          _2039_lhsGen = _out97;
          _2040_needsIIFE = _out98;
          _2041_recIdents = _out99;
          RAST._IExpr _2042_exprGen;
          DCOMP._IOwnership _2043___v45;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2044_exprIdents;
          RAST._IExpr _out100;
          DCOMP._IOwnership _out101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
          (this).GenExpr(_2037_expression, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out100, out _out101, out _out102);
          _2042_exprGen = _out100;
          _2043___v45 = _out101;
          _2044_exprIdents = _out102;
          if (_2040_needsIIFE) {
            generated = RAST.Expr.create_Block(RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2042_exprGen)), RAST.Expr.create_RawExpr(_2039_lhsGen)));
          } else {
            generated = RAST.Expr.create_AssignVar(_2039_lhsGen, _2042_exprGen);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2041_recIdents, _2044_exprIdents);
        }
      } else if (_source67.is_If) {
        DAST._IExpression _2045___mcc_h6 = _source67.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2046___mcc_h7 = _source67.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _2047___mcc_h8 = _source67.dtor_els;
        Dafny.ISequence<DAST._IStatement> _2048_els = _2047___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _2049_thn = _2046___mcc_h7;
        DAST._IExpression _2050_cond = _2045___mcc_h6;
        {
          RAST._IExpr _2051_cond;
          DCOMP._IOwnership _2052___v46;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2053_recIdents;
          RAST._IExpr _out103;
          DCOMP._IOwnership _out104;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
          (this).GenExpr(_2050_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out103, out _out104, out _out105);
          _2051_cond = _out103;
          _2052___v46 = _out104;
          _2053_recIdents = _out105;
          Dafny.ISequence<Dafny.Rune> _2054_condString;
          _2054_condString = (_2051_cond)._ToString(DCOMP.__default.IND);
          readIdents = _2053_recIdents;
          RAST._IExpr _2055_thn;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2056_thnIdents;
          RAST._IExpr _out106;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
          (this).GenStmts(_2049_thn, selfIdent, @params, isLast, earlyReturn, out _out106, out _out107);
          _2055_thn = _out106;
          _2056_thnIdents = _out107;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2056_thnIdents);
          RAST._IExpr _2057_els;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2058_elsIdents;
          RAST._IExpr _out108;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out109;
          (this).GenStmts(_2048_els, selfIdent, @params, isLast, earlyReturn, out _out108, out _out109);
          _2057_els = _out108;
          _2058_elsIdents = _out109;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2058_elsIdents);
          generated = RAST.Expr.create_IfExpr(_2051_cond, _2055_thn, _2057_els);
        }
      } else if (_source67.is_Labeled) {
        Dafny.ISequence<Dafny.Rune> _2059___mcc_h9 = _source67.dtor_lbl;
        Dafny.ISequence<DAST._IStatement> _2060___mcc_h10 = _source67.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2061_body = _2060___mcc_h10;
        Dafny.ISequence<Dafny.Rune> _2062_lbl = _2059___mcc_h9;
        {
          RAST._IExpr _2063_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2064_bodyIdents;
          RAST._IExpr _out110;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
          (this).GenStmts(_2061_body, selfIdent, @params, isLast, earlyReturn, out _out110, out _out111);
          _2063_body = _out110;
          _2064_bodyIdents = _out111;
          readIdents = _2064_bodyIdents;
          generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2062_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_2063_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
        }
      } else if (_source67.is_While) {
        DAST._IExpression _2065___mcc_h11 = _source67.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2066___mcc_h12 = _source67.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2067_body = _2066___mcc_h12;
        DAST._IExpression _2068_cond = _2065___mcc_h11;
        {
          RAST._IExpr _2069_cond;
          DCOMP._IOwnership _2070___v47;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2071_recIdents;
          RAST._IExpr _out112;
          DCOMP._IOwnership _out113;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
          (this).GenExpr(_2068_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out112, out _out113, out _out114);
          _2069_cond = _out112;
          _2070___v47 = _out113;
          _2071_recIdents = _out114;
          readIdents = _2071_recIdents;
          RAST._IExpr _2072_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2073_bodyIdents;
          RAST._IExpr _out115;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
          (this).GenStmts(_2067_body, selfIdent, @params, false, earlyReturn, out _out115, out _out116);
          _2072_body = _out115;
          _2073_bodyIdents = _out116;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2073_bodyIdents);
          generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2069_cond), _2072_body);
        }
      } else if (_source67.is_Foreach) {
        Dafny.ISequence<Dafny.Rune> _2074___mcc_h13 = _source67.dtor_boundName;
        DAST._IType _2075___mcc_h14 = _source67.dtor_boundType;
        DAST._IExpression _2076___mcc_h15 = _source67.dtor_over;
        Dafny.ISequence<DAST._IStatement> _2077___mcc_h16 = _source67.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2078_body = _2077___mcc_h16;
        DAST._IExpression _2079_over = _2076___mcc_h15;
        DAST._IType _2080_boundType = _2075___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _2081_boundName = _2074___mcc_h13;
        {
          RAST._IExpr _2082_over;
          DCOMP._IOwnership _2083___v48;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2084_recIdents;
          RAST._IExpr _out117;
          DCOMP._IOwnership _out118;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
          (this).GenExpr(_2079_over, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out117, out _out118, out _out119);
          _2082_over = _out117;
          _2083___v48 = _out118;
          _2084_recIdents = _out119;
          RAST._IType _2085_boundTypeStr;
          RAST._IType _out120;
          _out120 = (this).GenType(_2080_boundType, false, false);
          _2085_boundTypeStr = _out120;
          readIdents = _2084_recIdents;
          RAST._IExpr _2086_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2087_bodyIdents;
          RAST._IExpr _out121;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
          (this).GenStmts(_2078_body, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2081_boundName)), false, earlyReturn, out _out121, out _out122);
          _2086_body = _out121;
          _2087_bodyIdents = _out122;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2087_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2081_boundName));
          generated = RAST.Expr.create_For(DCOMP.__default.escapeIdent(_2081_boundName), _2082_over, _2086_body);
        }
      } else if (_source67.is_Call) {
        DAST._IExpression _2088___mcc_h17 = _source67.dtor_on;
        DAST._ICallName _2089___mcc_h18 = _source67.dtor_callName;
        Dafny.ISequence<DAST._IType> _2090___mcc_h19 = _source67.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2091___mcc_h20 = _source67.dtor_args;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2092___mcc_h21 = _source67.dtor_outs;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2093_maybeOutVars = _2092___mcc_h21;
        Dafny.ISequence<DAST._IExpression> _2094_args = _2091___mcc_h20;
        Dafny.ISequence<DAST._IType> _2095_typeArgs = _2090___mcc_h19;
        DAST._ICallName _2096_name = _2089___mcc_h18;
        DAST._IExpression _2097_on = _2088___mcc_h17;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2098_typeArgString;
          _2098_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_2095_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2099_typeI;
            _2099_typeI = BigInteger.Zero;
            Dafny.ISequence<RAST._IType> _2100_typeArgsR;
            _2100_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            while ((_2099_typeI) < (new BigInteger((_2095_typeArgs).Count))) {
              RAST._IType _2101_tpe;
              RAST._IType _out123;
              _out123 = (this).GenType((_2095_typeArgs).Select(_2099_typeI), false, false);
              _2101_tpe = _out123;
              _2100_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_2100_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_2101_tpe));
              _2099_typeI = (_2099_typeI) + (BigInteger.One);
            }
            _2098_typeArgString = (RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2100_typeArgsR))._ToString(DCOMP.__default.IND);
          }
          Dafny.ISequence<Dafny.Rune> _2102_argString;
          _2102_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2103_i;
          _2103_i = BigInteger.Zero;
          while ((_2103_i) < (new BigInteger((_2094_args).Count))) {
            if ((_2103_i).Sign == 1) {
              _2102_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2102_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IExpr _2104_argExpr;
            DCOMP._IOwnership _2105_ownership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2106_argIdents;
            RAST._IExpr _out124;
            DCOMP._IOwnership _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            (this).GenExpr((_2094_args).Select(_2103_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out124, out _out125, out _out126);
            _2104_argExpr = _out124;
            _2105_ownership = _out125;
            _2106_argIdents = _out126;
            Dafny.ISequence<Dafny.Rune> _2107_argExprString;
            _2107_argExprString = (_2104_argExpr)._ToString(DCOMP.__default.IND);
            _2102_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2102_argString, _2107_argExprString);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2106_argIdents);
            _2103_i = (_2103_i) + (BigInteger.One);
          }
          RAST._IExpr _2108_onExpr;
          DCOMP._IOwnership _2109___v49;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2110_enclosingIdents;
          RAST._IExpr _out127;
          DCOMP._IOwnership _out128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out129;
          (this).GenExpr(_2097_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out127, out _out128, out _out129);
          _2108_onExpr = _out127;
          _2109___v49 = _out128;
          _2110_enclosingIdents = _out129;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2110_enclosingIdents);
          Dafny.ISequence<Dafny.Rune> _2111_enclosingString;
          _2111_enclosingString = (_2108_onExpr)._ToString(DCOMP.__default.IND);
          DAST._IExpression _source69 = _2097_on;
          if (_source69.is_Literal) {
            DAST._ILiteral _2112___mcc_h26 = _source69.dtor_Literal_a0;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2113___mcc_h28 = _source69.dtor_Ident_a0;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2114___mcc_h30 = _source69.dtor_Companion_a0;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_2111_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source69.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2115___mcc_h32 = _source69.dtor_Tuple_a0;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2116___mcc_h34 = _source69.dtor_path;
            Dafny.ISequence<DAST._IType> _2117___mcc_h35 = _source69.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2118___mcc_h36 = _source69.dtor_args;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2119___mcc_h40 = _source69.dtor_dims;
            DAST._IType _2120___mcc_h41 = _source69.dtor_typ;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2121___mcc_h44 = _source69.dtor_path;
            Dafny.ISequence<DAST._IType> _2122___mcc_h45 = _source69.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2123___mcc_h46 = _source69.dtor_variant;
            bool _2124___mcc_h47 = _source69.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2125___mcc_h48 = _source69.dtor_contents;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_Convert) {
            DAST._IExpression _2126___mcc_h54 = _source69.dtor_value;
            DAST._IType _2127___mcc_h55 = _source69.dtor_from;
            DAST._IType _2128___mcc_h56 = _source69.dtor_typ;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_SeqConstruct) {
            DAST._IExpression _2129___mcc_h60 = _source69.dtor_length;
            DAST._IExpression _2130___mcc_h61 = _source69.dtor_elem;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2131___mcc_h64 = _source69.dtor_elements;
            DAST._IType _2132___mcc_h65 = _source69.dtor_typ;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2133___mcc_h68 = _source69.dtor_elements;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _2134___mcc_h70 = _source69.dtor_elements;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2135___mcc_h72 = _source69.dtor_mapElems;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_MapBuilder) {
            DAST._IType _2136___mcc_h74 = _source69.dtor_keyType;
            DAST._IType _2137___mcc_h75 = _source69.dtor_valueType;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_SeqUpdate) {
            DAST._IExpression _2138___mcc_h78 = _source69.dtor_expr;
            DAST._IExpression _2139___mcc_h79 = _source69.dtor_indexExpr;
            DAST._IExpression _2140___mcc_h80 = _source69.dtor_value;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_MapUpdate) {
            DAST._IExpression _2141___mcc_h84 = _source69.dtor_expr;
            DAST._IExpression _2142___mcc_h85 = _source69.dtor_indexExpr;
            DAST._IExpression _2143___mcc_h86 = _source69.dtor_value;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_SetBuilder) {
            DAST._IType _2144___mcc_h90 = _source69.dtor_elemType;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_ToMultiset) {
            DAST._IExpression _2145___mcc_h92 = _source69.dtor_ToMultiset_a0;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_This) {
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_Ite) {
            DAST._IExpression _2146___mcc_h94 = _source69.dtor_cond;
            DAST._IExpression _2147___mcc_h95 = _source69.dtor_thn;
            DAST._IExpression _2148___mcc_h96 = _source69.dtor_els;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_UnOp) {
            DAST._IUnaryOp _2149___mcc_h100 = _source69.dtor_unOp;
            DAST._IExpression _2150___mcc_h101 = _source69.dtor_expr;
            DAST.Format._IUnaryOpFormat _2151___mcc_h102 = _source69.dtor_format1;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_BinOp) {
            DAST._IBinOp _2152___mcc_h106 = _source69.dtor_op;
            DAST._IExpression _2153___mcc_h107 = _source69.dtor_left;
            DAST._IExpression _2154___mcc_h108 = _source69.dtor_right;
            DAST.Format._IBinaryOpFormat _2155___mcc_h109 = _source69.dtor_format2;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_ArrayLen) {
            DAST._IExpression _2156___mcc_h114 = _source69.dtor_expr;
            BigInteger _2157___mcc_h115 = _source69.dtor_dim;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_MapKeys) {
            DAST._IExpression _2158___mcc_h118 = _source69.dtor_expr;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_MapValues) {
            DAST._IExpression _2159___mcc_h120 = _source69.dtor_expr;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_Select) {
            DAST._IExpression _2160___mcc_h122 = _source69.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2161___mcc_h123 = _source69.dtor_field;
            bool _2162___mcc_h124 = _source69.dtor_isConstant;
            bool _2163___mcc_h125 = _source69.dtor_onDatatype;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_SelectFn) {
            DAST._IExpression _2164___mcc_h130 = _source69.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2165___mcc_h131 = _source69.dtor_field;
            bool _2166___mcc_h132 = _source69.dtor_onDatatype;
            bool _2167___mcc_h133 = _source69.dtor_isStatic;
            BigInteger _2168___mcc_h134 = _source69.dtor_arity;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_Index) {
            DAST._IExpression _2169___mcc_h140 = _source69.dtor_expr;
            DAST._ICollKind _2170___mcc_h141 = _source69.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _2171___mcc_h142 = _source69.dtor_indices;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_IndexRange) {
            DAST._IExpression _2172___mcc_h146 = _source69.dtor_expr;
            bool _2173___mcc_h147 = _source69.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _2174___mcc_h148 = _source69.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _2175___mcc_h149 = _source69.dtor_high;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_TupleSelect) {
            DAST._IExpression _2176___mcc_h154 = _source69.dtor_expr;
            BigInteger _2177___mcc_h155 = _source69.dtor_index;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_Call) {
            DAST._IExpression _2178___mcc_h158 = _source69.dtor_on;
            DAST._ICallName _2179___mcc_h159 = _source69.dtor_callName;
            Dafny.ISequence<DAST._IType> _2180___mcc_h160 = _source69.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2181___mcc_h161 = _source69.dtor_args;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2182___mcc_h166 = _source69.dtor_params;
            DAST._IType _2183___mcc_h167 = _source69.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2184___mcc_h168 = _source69.dtor_body;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2185___mcc_h172 = _source69.dtor_values;
            DAST._IType _2186___mcc_h173 = _source69.dtor_retType;
            DAST._IExpression _2187___mcc_h174 = _source69.dtor_expr;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2188___mcc_h178 = _source69.dtor_name;
            DAST._IType _2189___mcc_h179 = _source69.dtor_typ;
            DAST._IExpression _2190___mcc_h180 = _source69.dtor_value;
            DAST._IExpression _2191___mcc_h181 = _source69.dtor_iifeBody;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_Apply) {
            DAST._IExpression _2192___mcc_h186 = _source69.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2193___mcc_h187 = _source69.dtor_args;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_TypeTest) {
            DAST._IExpression _2194___mcc_h190 = _source69.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2195___mcc_h191 = _source69.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2196___mcc_h192 = _source69.dtor_variant;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_InitializationValue) {
            DAST._IType _2197___mcc_h196 = _source69.dtor_typ;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_BoolBoundedPool) {
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_SetBoundedPool) {
            DAST._IExpression _2198___mcc_h198 = _source69.dtor_of;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source69.is_SeqBoundedPool) {
            DAST._IExpression _2199___mcc_h200 = _source69.dtor_of;
            bool _2200___mcc_h201 = _source69.dtor_includeDuplicates;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IExpression _2201___mcc_h204 = _source69.dtor_lo;
            DAST._IExpression _2202___mcc_h205 = _source69.dtor_hi;
            {
              _2111_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2111_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _2203_receiver;
          _2203_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source70 = _2093_maybeOutVars;
          if (_source70.is_None) {
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2204___mcc_h208 = _source70.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2205_outVars = _2204___mcc_h208;
            {
              if ((new BigInteger((_2205_outVars).Count)) > (BigInteger.One)) {
                _2203_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _2206_outI;
              _2206_outI = BigInteger.Zero;
              while ((_2206_outI) < (new BigInteger((_2205_outVars).Count))) {
                if ((_2206_outI).Sign == 1) {
                  _2203_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_2203_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _2207_outVar;
                _2207_outVar = (_2205_outVars).Select(_2206_outI);
                _2203_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_2203_receiver, (_2207_outVar));
                _2206_outI = (_2206_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_2205_outVars).Count)) > (BigInteger.One)) {
                _2203_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_2203_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          }
          Dafny.ISequence<Dafny.Rune> _2208_renderedName;
          _2208_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source71) => {
            if (_source71.is_Name) {
              Dafny.ISequence<Dafny.Rune> _2209___mcc_h209 = _source71.dtor_name;
              Dafny.ISequence<Dafny.Rune> _2210_name = _2209___mcc_h209;
              return DCOMP.__default.escapeIdent(_2210_name);
            } else if (_source71.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source71.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source71.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_2096_name);
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_2203_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_2203_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _2111_enclosingString), _2208_renderedName), _2098_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2102_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");")));
        }
      } else if (_source67.is_Return) {
        DAST._IExpression _2211___mcc_h22 = _source67.dtor_expr;
        DAST._IExpression _2212_expr = _2211___mcc_h22;
        {
          RAST._IExpr _2213_expr;
          DCOMP._IOwnership _2214___v52;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2215_recIdents;
          RAST._IExpr _out130;
          DCOMP._IOwnership _out131;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
          (this).GenExpr(_2212_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out130, out _out131, out _out132);
          _2213_expr = _out130;
          _2214___v52 = _out131;
          _2215_recIdents = _out132;
          readIdents = _2215_recIdents;
          if (isLast) {
            generated = _2213_expr;
          } else {
            generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2213_expr));
          }
        }
      } else if (_source67.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source67.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2216___mcc_h23 = _source67.dtor_toLabel;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2217_toLabel = _2216___mcc_h23;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source72 = _2217_toLabel;
          if (_source72.is_None) {
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2218___mcc_h210 = _source72.dtor_value;
            Dafny.ISequence<Dafny.Rune> _2219_lbl = _2218___mcc_h210;
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2219_lbl)));
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source67.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _2220___mcc_h24 = _source67.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2221_body = _2220___mcc_h24;
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self.clone()")))));
          }
          BigInteger _2222_paramI;
          _2222_paramI = BigInteger.Zero;
          while ((_2222_paramI) < (new BigInteger((@params).Count))) {
            Dafny.ISequence<Dafny.Rune> _2223_param;
            _2223_param = (@params).Select(_2222_paramI);
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_2223_param), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.Clone(RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent(_2223_param))))));
            _2222_paramI = (_2222_paramI) + (BigInteger.One);
          }
          RAST._IExpr _2224_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2225_bodyIdents;
          RAST._IExpr _out133;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
          (this).GenStmts(_2221_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out133, out _out134);
          _2224_body = _out133;
          _2225_bodyIdents = _out134;
          readIdents = _2225_bodyIdents;
          generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _2224_body)));
        }
      } else if (_source67.is_JumpTailCallStart) {
        {
          generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source67.is_Halt) {
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else {
        DAST._IExpression _2226___mcc_h25 = _source67.dtor_Print_a0;
        DAST._IExpression _2227_e = _2226___mcc_h25;
        {
          RAST._IExpr _2228_printedExpr;
          DCOMP._IOwnership _2229_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2230_recIdents;
          RAST._IExpr _out135;
          DCOMP._IOwnership _out136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
          (this).GenExpr(_2227_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out135, out _out136, out _out137);
          _2228_printedExpr = _out135;
          _2229_recOwnership = _out136;
          _2230_recIdents = _out137;
          Dafny.ISequence<Dafny.Rune> _2231_printedExprString;
          _2231_printedExprString = (_2228_printedExpr)._ToString(DCOMP.__default.IND);
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), _2231_printedExprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));")));
          readIdents = _2230_recIdents;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source73 = range;
      if (_source73.is_U8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
      } else if (_source73.is_I8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
      } else if (_source73.is_U16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
      } else if (_source73.is_I16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
      } else if (_source73.is_U32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
      } else if (_source73.is_I32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
      } else if (_source73.is_U64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
      } else if (_source73.is_I64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
      } else if (_source73.is_U128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
      } else if (_source73.is_I128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
      } else if (_source73.is_BigInt) {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      } else {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public static void FromOwned(RAST._IExpr r, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
        @out = r;
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
        @out = RAST.__default.Borrow(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        @out = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      }
    }
    public static void FromOwnership(RAST._IExpr r, DCOMP._IOwnership ownership, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwned())) {
        RAST._IExpr _out138;
        DCOMP._IOwnership _out139;
        DCOMP.COMP.FromOwned(r, expectedOwnership, out _out138, out _out139);
        @out = _out138;
        resultingOwnership = _out139;
        return ;
      } else if ((object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowedMut()))) {
        if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          @out = RAST.__default.Clone(r);
        } else if ((object.Equals(expectedOwnership, ownership)) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
          resultingOwnership = ownership;
          @out = r;
        } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) && (object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowedMut()))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          @out = r;
        } else {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
          @out = RAST.__default.BorrowMut(r);
        }
      } else {
      }
    }
    public static bool OwnershipGuarantee(DCOMP._IOwnership expectedOwnership, DCOMP._IOwnership resultingOwnership)
    {
      return (!(!object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) || (object.Equals(resultingOwnership, expectedOwnership))) && (!object.Equals(resultingOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()));
    }
    public void GenExprLiteral(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source74 = e;
      DAST._ILiteral _2232___mcc_h0 = _source74.dtor_Literal_a0;
      DAST._ILiteral _source75 = _2232___mcc_h0;
      if (_source75.is_BoolLiteral) {
        bool _2233___mcc_h1 = _source75.dtor_BoolLiteral_a0;
        if ((_2233___mcc_h1) == (false)) {
          {
            RAST._IExpr _out140;
            DCOMP._IOwnership _out141;
            DCOMP.COMP.FromOwned(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")), expectedOwnership, out _out140, out _out141);
            r = _out140;
            resultingOwnership = _out141;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        } else {
          {
            RAST._IExpr _out142;
            DCOMP._IOwnership _out143;
            DCOMP.COMP.FromOwned(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")), expectedOwnership, out _out142, out _out143);
            r = _out142;
            resultingOwnership = _out143;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      } else if (_source75.is_IntLiteral) {
        Dafny.ISequence<Dafny.Rune> _2234___mcc_h2 = _source75.dtor_IntLiteral_a0;
        DAST._IType _2235___mcc_h3 = _source75.dtor_IntLiteral_a1;
        DAST._IType _2236_t = _2235___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _2237_i = _2234___mcc_h2;
        {
          DAST._IType _source76 = _2236_t;
          if (_source76.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2238___mcc_h100 = _source76.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2239___mcc_h101 = _source76.dtor_typeArgs;
            DAST._IResolvedType _2240___mcc_h102 = _source76.dtor_resolved;
            DAST._IType _2241_o = _2236_t;
            {
              RAST._IType _2242_genType;
              RAST._IType _out144;
              _out144 = (this).GenType(_2241_o, false, false);
              _2242_genType = _out144;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2242_genType);
            }
          } else if (_source76.is_Nullable) {
            DAST._IType _2243___mcc_h106 = _source76.dtor_Nullable_a0;
            DAST._IType _2244_o = _2236_t;
            {
              RAST._IType _2245_genType;
              RAST._IType _out145;
              _out145 = (this).GenType(_2244_o, false, false);
              _2245_genType = _out145;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2245_genType);
            }
          } else if (_source76.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2246___mcc_h108 = _source76.dtor_Tuple_a0;
            DAST._IType _2247_o = _2236_t;
            {
              RAST._IType _2248_genType;
              RAST._IType _out146;
              _out146 = (this).GenType(_2247_o, false, false);
              _2248_genType = _out146;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2248_genType);
            }
          } else if (_source76.is_Array) {
            DAST._IType _2249___mcc_h110 = _source76.dtor_element;
            BigInteger _2250___mcc_h111 = _source76.dtor_dims;
            DAST._IType _2251_o = _2236_t;
            {
              RAST._IType _2252_genType;
              RAST._IType _out147;
              _out147 = (this).GenType(_2251_o, false, false);
              _2252_genType = _out147;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2252_genType);
            }
          } else if (_source76.is_Seq) {
            DAST._IType _2253___mcc_h114 = _source76.dtor_element;
            DAST._IType _2254_o = _2236_t;
            {
              RAST._IType _2255_genType;
              RAST._IType _out148;
              _out148 = (this).GenType(_2254_o, false, false);
              _2255_genType = _out148;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2255_genType);
            }
          } else if (_source76.is_Set) {
            DAST._IType _2256___mcc_h116 = _source76.dtor_element;
            DAST._IType _2257_o = _2236_t;
            {
              RAST._IType _2258_genType;
              RAST._IType _out149;
              _out149 = (this).GenType(_2257_o, false, false);
              _2258_genType = _out149;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2258_genType);
            }
          } else if (_source76.is_Multiset) {
            DAST._IType _2259___mcc_h118 = _source76.dtor_element;
            DAST._IType _2260_o = _2236_t;
            {
              RAST._IType _2261_genType;
              RAST._IType _out150;
              _out150 = (this).GenType(_2260_o, false, false);
              _2261_genType = _out150;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2261_genType);
            }
          } else if (_source76.is_Map) {
            DAST._IType _2262___mcc_h120 = _source76.dtor_key;
            DAST._IType _2263___mcc_h121 = _source76.dtor_value;
            DAST._IType _2264_o = _2236_t;
            {
              RAST._IType _2265_genType;
              RAST._IType _out151;
              _out151 = (this).GenType(_2264_o, false, false);
              _2265_genType = _out151;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2265_genType);
            }
          } else if (_source76.is_SetBuilder) {
            DAST._IType _2266___mcc_h124 = _source76.dtor_element;
            DAST._IType _2267_o = _2236_t;
            {
              RAST._IType _2268_genType;
              RAST._IType _out152;
              _out152 = (this).GenType(_2267_o, false, false);
              _2268_genType = _out152;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2268_genType);
            }
          } else if (_source76.is_MapBuilder) {
            DAST._IType _2269___mcc_h126 = _source76.dtor_key;
            DAST._IType _2270___mcc_h127 = _source76.dtor_value;
            DAST._IType _2271_o = _2236_t;
            {
              RAST._IType _2272_genType;
              RAST._IType _out153;
              _out153 = (this).GenType(_2271_o, false, false);
              _2272_genType = _out153;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2272_genType);
            }
          } else if (_source76.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2273___mcc_h130 = _source76.dtor_args;
            DAST._IType _2274___mcc_h131 = _source76.dtor_result;
            DAST._IType _2275_o = _2236_t;
            {
              RAST._IType _2276_genType;
              RAST._IType _out154;
              _out154 = (this).GenType(_2275_o, false, false);
              _2276_genType = _out154;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2276_genType);
            }
          } else if (_source76.is_Primitive) {
            DAST._IPrimitive _2277___mcc_h134 = _source76.dtor_Primitive_a0;
            DAST._IPrimitive _source77 = _2277___mcc_h134;
            if (_source77.is_Int) {
              {
                if ((new BigInteger((_2237_i).Count)) <= (new BigInteger(4))) {
                  r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(RAST.Expr.create_LiteralInt(_2237_i));
                } else {
                  r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(RAST.Expr.create_LiteralString(_2237_i, true));
                }
              }
            } else if (_source77.is_Real) {
              DAST._IType _2278_o = _2236_t;
              {
                RAST._IType _2279_genType;
                RAST._IType _out155;
                _out155 = (this).GenType(_2278_o, false, false);
                _2279_genType = _out155;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2279_genType);
              }
            } else if (_source77.is_String) {
              DAST._IType _2280_o = _2236_t;
              {
                RAST._IType _2281_genType;
                RAST._IType _out156;
                _out156 = (this).GenType(_2280_o, false, false);
                _2281_genType = _out156;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2281_genType);
              }
            } else if (_source77.is_Bool) {
              DAST._IType _2282_o = _2236_t;
              {
                RAST._IType _2283_genType;
                RAST._IType _out157;
                _out157 = (this).GenType(_2282_o, false, false);
                _2283_genType = _out157;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2283_genType);
              }
            } else {
              DAST._IType _2284_o = _2236_t;
              {
                RAST._IType _2285_genType;
                RAST._IType _out158;
                _out158 = (this).GenType(_2284_o, false, false);
                _2285_genType = _out158;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2285_genType);
              }
            }
          } else if (_source76.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2286___mcc_h136 = _source76.dtor_Passthrough_a0;
            DAST._IType _2287_o = _2236_t;
            {
              RAST._IType _2288_genType;
              RAST._IType _out159;
              _out159 = (this).GenType(_2287_o, false, false);
              _2288_genType = _out159;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2288_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2289___mcc_h138 = _source76.dtor_TypeArg_a0;
            DAST._IType _2290_o = _2236_t;
            {
              RAST._IType _2291_genType;
              RAST._IType _out160;
              _out160 = (this).GenType(_2290_o, false, false);
              _2291_genType = _out160;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2237_i), _2291_genType);
            }
          }
          RAST._IExpr _out161;
          DCOMP._IOwnership _out162;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out161, out _out162);
          r = _out161;
          resultingOwnership = _out162;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source75.is_DecLiteral) {
        Dafny.ISequence<Dafny.Rune> _2292___mcc_h4 = _source75.dtor_DecLiteral_a0;
        Dafny.ISequence<Dafny.Rune> _2293___mcc_h5 = _source75.dtor_DecLiteral_a1;
        DAST._IType _2294___mcc_h6 = _source75.dtor_DecLiteral_a2;
        DAST._IType _2295_t = _2294___mcc_h6;
        Dafny.ISequence<Dafny.Rune> _2296_d = _2293___mcc_h5;
        Dafny.ISequence<Dafny.Rune> _2297_n = _2292___mcc_h4;
        {
          DAST._IType _source78 = _2295_t;
          if (_source78.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2298___mcc_h140 = _source78.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2299___mcc_h141 = _source78.dtor_typeArgs;
            DAST._IResolvedType _2300___mcc_h142 = _source78.dtor_resolved;
            DAST._IType _2301_o = _2295_t;
            {
              RAST._IType _2302_genType;
              RAST._IType _out163;
              _out163 = (this).GenType(_2301_o, false, false);
              _2302_genType = _out163;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2302_genType);
            }
          } else if (_source78.is_Nullable) {
            DAST._IType _2303___mcc_h146 = _source78.dtor_Nullable_a0;
            DAST._IType _2304_o = _2295_t;
            {
              RAST._IType _2305_genType;
              RAST._IType _out164;
              _out164 = (this).GenType(_2304_o, false, false);
              _2305_genType = _out164;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2305_genType);
            }
          } else if (_source78.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2306___mcc_h148 = _source78.dtor_Tuple_a0;
            DAST._IType _2307_o = _2295_t;
            {
              RAST._IType _2308_genType;
              RAST._IType _out165;
              _out165 = (this).GenType(_2307_o, false, false);
              _2308_genType = _out165;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2308_genType);
            }
          } else if (_source78.is_Array) {
            DAST._IType _2309___mcc_h150 = _source78.dtor_element;
            BigInteger _2310___mcc_h151 = _source78.dtor_dims;
            DAST._IType _2311_o = _2295_t;
            {
              RAST._IType _2312_genType;
              RAST._IType _out166;
              _out166 = (this).GenType(_2311_o, false, false);
              _2312_genType = _out166;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2312_genType);
            }
          } else if (_source78.is_Seq) {
            DAST._IType _2313___mcc_h154 = _source78.dtor_element;
            DAST._IType _2314_o = _2295_t;
            {
              RAST._IType _2315_genType;
              RAST._IType _out167;
              _out167 = (this).GenType(_2314_o, false, false);
              _2315_genType = _out167;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2315_genType);
            }
          } else if (_source78.is_Set) {
            DAST._IType _2316___mcc_h156 = _source78.dtor_element;
            DAST._IType _2317_o = _2295_t;
            {
              RAST._IType _2318_genType;
              RAST._IType _out168;
              _out168 = (this).GenType(_2317_o, false, false);
              _2318_genType = _out168;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2318_genType);
            }
          } else if (_source78.is_Multiset) {
            DAST._IType _2319___mcc_h158 = _source78.dtor_element;
            DAST._IType _2320_o = _2295_t;
            {
              RAST._IType _2321_genType;
              RAST._IType _out169;
              _out169 = (this).GenType(_2320_o, false, false);
              _2321_genType = _out169;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2321_genType);
            }
          } else if (_source78.is_Map) {
            DAST._IType _2322___mcc_h160 = _source78.dtor_key;
            DAST._IType _2323___mcc_h161 = _source78.dtor_value;
            DAST._IType _2324_o = _2295_t;
            {
              RAST._IType _2325_genType;
              RAST._IType _out170;
              _out170 = (this).GenType(_2324_o, false, false);
              _2325_genType = _out170;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2325_genType);
            }
          } else if (_source78.is_SetBuilder) {
            DAST._IType _2326___mcc_h164 = _source78.dtor_element;
            DAST._IType _2327_o = _2295_t;
            {
              RAST._IType _2328_genType;
              RAST._IType _out171;
              _out171 = (this).GenType(_2327_o, false, false);
              _2328_genType = _out171;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2328_genType);
            }
          } else if (_source78.is_MapBuilder) {
            DAST._IType _2329___mcc_h166 = _source78.dtor_key;
            DAST._IType _2330___mcc_h167 = _source78.dtor_value;
            DAST._IType _2331_o = _2295_t;
            {
              RAST._IType _2332_genType;
              RAST._IType _out172;
              _out172 = (this).GenType(_2331_o, false, false);
              _2332_genType = _out172;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2332_genType);
            }
          } else if (_source78.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2333___mcc_h170 = _source78.dtor_args;
            DAST._IType _2334___mcc_h171 = _source78.dtor_result;
            DAST._IType _2335_o = _2295_t;
            {
              RAST._IType _2336_genType;
              RAST._IType _out173;
              _out173 = (this).GenType(_2335_o, false, false);
              _2336_genType = _out173;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2336_genType);
            }
          } else if (_source78.is_Primitive) {
            DAST._IPrimitive _2337___mcc_h174 = _source78.dtor_Primitive_a0;
            DAST._IPrimitive _source79 = _2337___mcc_h174;
            if (_source79.is_Int) {
              DAST._IType _2338_o = _2295_t;
              {
                RAST._IType _2339_genType;
                RAST._IType _out174;
                _out174 = (this).GenType(_2338_o, false, false);
                _2339_genType = _out174;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2339_genType);
              }
            } else if (_source79.is_Real) {
              {
                r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
              }
            } else if (_source79.is_String) {
              DAST._IType _2340_o = _2295_t;
              {
                RAST._IType _2341_genType;
                RAST._IType _out175;
                _out175 = (this).GenType(_2340_o, false, false);
                _2341_genType = _out175;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2341_genType);
              }
            } else if (_source79.is_Bool) {
              DAST._IType _2342_o = _2295_t;
              {
                RAST._IType _2343_genType;
                RAST._IType _out176;
                _out176 = (this).GenType(_2342_o, false, false);
                _2343_genType = _out176;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2343_genType);
              }
            } else {
              DAST._IType _2344_o = _2295_t;
              {
                RAST._IType _2345_genType;
                RAST._IType _out177;
                _out177 = (this).GenType(_2344_o, false, false);
                _2345_genType = _out177;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2345_genType);
              }
            }
          } else if (_source78.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2346___mcc_h176 = _source78.dtor_Passthrough_a0;
            DAST._IType _2347_o = _2295_t;
            {
              RAST._IType _2348_genType;
              RAST._IType _out178;
              _out178 = (this).GenType(_2347_o, false, false);
              _2348_genType = _out178;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2348_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2349___mcc_h178 = _source78.dtor_TypeArg_a0;
            DAST._IType _2350_o = _2295_t;
            {
              RAST._IType _2351_genType;
              RAST._IType _out179;
              _out179 = (this).GenType(_2350_o, false, false);
              _2351_genType = _out179;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2297_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2296_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2351_genType);
            }
          }
          RAST._IExpr _out180;
          DCOMP._IOwnership _out181;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out180, out _out181);
          r = _out180;
          resultingOwnership = _out181;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source75.is_StringLiteral) {
        Dafny.ISequence<Dafny.Rune> _2352___mcc_h7 = _source75.dtor_StringLiteral_a0;
        Dafny.ISequence<Dafny.Rune> _2353_l = _2352___mcc_h7;
        {
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_of"))).Apply1(RAST.Expr.create_LiteralString(_2353_l, false));
          RAST._IExpr _out182;
          DCOMP._IOwnership _out183;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out182, out _out183);
          r = _out182;
          resultingOwnership = _out183;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source75.is_CharLiteral) {
        Dafny.Rune _2354___mcc_h8 = _source75.dtor_CharLiteral_a0;
        Dafny.Rune _2355_c = _2354___mcc_h8;
        {
          r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_2355_c).Value)));
          if (!((this).UnicodeChars)) {
            r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u16"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          } else {
            r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          }
          r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
          RAST._IExpr _out184;
          DCOMP._IOwnership _out185;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out184, out _out185);
          r = _out184;
          resultingOwnership = _out185;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else {
        DAST._IType _2356___mcc_h9 = _source75.dtor_Null_a0;
        DAST._IType _2357_tpe = _2356___mcc_h9;
        {
          RAST._IType _2358_tpeGen;
          RAST._IType _out186;
          _out186 = (this).GenType(_2357_tpe, false, false);
          _2358_tpeGen = _out186;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _2358_tpeGen);
          RAST._IExpr _out187;
          DCOMP._IOwnership _out188;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out187, out _out188);
          r = _out187;
          resultingOwnership = _out188;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      }
    }
    public void GenExprBinary(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs49 = e;
      DAST._IBinOp _2359_op = _let_tmp_rhs49.dtor_op;
      DAST._IExpression _2360_lExpr = _let_tmp_rhs49.dtor_left;
      DAST._IExpression _2361_rExpr = _let_tmp_rhs49.dtor_right;
      DAST.Format._IBinaryOpFormat _2362_format = _let_tmp_rhs49.dtor_format2;
      bool _2363_becomesLeftCallsRight;
      _2363_becomesLeftCallsRight = ((System.Func<DAST._IBinOp, bool>)((_source80) => {
        if (_source80.is_Eq) {
          bool _2364___mcc_h0 = _source80.dtor_referential;
          bool _2365___mcc_h1 = _source80.dtor_nullable;
          return false;
        } else if (_source80.is_Div) {
          return false;
        } else if (_source80.is_EuclidianDiv) {
          return false;
        } else if (_source80.is_Mod) {
          return false;
        } else if (_source80.is_EuclidianMod) {
          return false;
        } else if (_source80.is_Lt) {
          return false;
        } else if (_source80.is_LtChar) {
          return false;
        } else if (_source80.is_Plus) {
          return false;
        } else if (_source80.is_Minus) {
          return false;
        } else if (_source80.is_Times) {
          return false;
        } else if (_source80.is_BitwiseAnd) {
          return false;
        } else if (_source80.is_BitwiseOr) {
          return false;
        } else if (_source80.is_BitwiseXor) {
          return false;
        } else if (_source80.is_BitwiseShiftRight) {
          return false;
        } else if (_source80.is_BitwiseShiftLeft) {
          return false;
        } else if (_source80.is_And) {
          return false;
        } else if (_source80.is_Or) {
          return false;
        } else if (_source80.is_In) {
          return false;
        } else if (_source80.is_SeqProperPrefix) {
          return false;
        } else if (_source80.is_SeqPrefix) {
          return false;
        } else if (_source80.is_SetMerge) {
          return true;
        } else if (_source80.is_SetSubtraction) {
          return true;
        } else if (_source80.is_SetIntersection) {
          return true;
        } else if (_source80.is_Subset) {
          return false;
        } else if (_source80.is_ProperSubset) {
          return false;
        } else if (_source80.is_SetDisjoint) {
          return true;
        } else if (_source80.is_MapMerge) {
          return true;
        } else if (_source80.is_MapSubtraction) {
          return true;
        } else if (_source80.is_MultisetMerge) {
          return true;
        } else if (_source80.is_MultisetSubtraction) {
          return true;
        } else if (_source80.is_MultisetIntersection) {
          return true;
        } else if (_source80.is_Submultiset) {
          return false;
        } else if (_source80.is_ProperSubmultiset) {
          return false;
        } else if (_source80.is_MultisetDisjoint) {
          return true;
        } else if (_source80.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _2366___mcc_h4 = _source80.dtor_Passthrough_a0;
          return false;
        }
      }))(_2359_op);
      bool _2367_becomesRightCallsLeft;
      _2367_becomesRightCallsLeft = ((System.Func<DAST._IBinOp, bool>)((_source81) => {
        if (_source81.is_Eq) {
          bool _2368___mcc_h6 = _source81.dtor_referential;
          bool _2369___mcc_h7 = _source81.dtor_nullable;
          return false;
        } else if (_source81.is_Div) {
          return false;
        } else if (_source81.is_EuclidianDiv) {
          return false;
        } else if (_source81.is_Mod) {
          return false;
        } else if (_source81.is_EuclidianMod) {
          return false;
        } else if (_source81.is_Lt) {
          return false;
        } else if (_source81.is_LtChar) {
          return false;
        } else if (_source81.is_Plus) {
          return false;
        } else if (_source81.is_Minus) {
          return false;
        } else if (_source81.is_Times) {
          return false;
        } else if (_source81.is_BitwiseAnd) {
          return false;
        } else if (_source81.is_BitwiseOr) {
          return false;
        } else if (_source81.is_BitwiseXor) {
          return false;
        } else if (_source81.is_BitwiseShiftRight) {
          return false;
        } else if (_source81.is_BitwiseShiftLeft) {
          return false;
        } else if (_source81.is_And) {
          return false;
        } else if (_source81.is_Or) {
          return false;
        } else if (_source81.is_In) {
          return true;
        } else if (_source81.is_SeqProperPrefix) {
          return false;
        } else if (_source81.is_SeqPrefix) {
          return false;
        } else if (_source81.is_SetMerge) {
          return false;
        } else if (_source81.is_SetSubtraction) {
          return false;
        } else if (_source81.is_SetIntersection) {
          return false;
        } else if (_source81.is_Subset) {
          return false;
        } else if (_source81.is_ProperSubset) {
          return false;
        } else if (_source81.is_SetDisjoint) {
          return false;
        } else if (_source81.is_MapMerge) {
          return false;
        } else if (_source81.is_MapSubtraction) {
          return false;
        } else if (_source81.is_MultisetMerge) {
          return false;
        } else if (_source81.is_MultisetSubtraction) {
          return false;
        } else if (_source81.is_MultisetIntersection) {
          return false;
        } else if (_source81.is_Submultiset) {
          return false;
        } else if (_source81.is_ProperSubmultiset) {
          return false;
        } else if (_source81.is_MultisetDisjoint) {
          return false;
        } else if (_source81.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2370___mcc_h10 = _source81.dtor_Passthrough_a0;
          return false;
        }
      }))(_2359_op);
      bool _2371_becomesCallLeftRight;
      _2371_becomesCallLeftRight = ((System.Func<DAST._IBinOp, bool>)((_source82) => {
        if (_source82.is_Eq) {
          bool _2372___mcc_h12 = _source82.dtor_referential;
          bool _2373___mcc_h13 = _source82.dtor_nullable;
          if ((_2372___mcc_h12) == (true)) {
            if ((_2373___mcc_h13) == (false)) {
              return true;
            } else {
              return false;
            }
          } else {
            return false;
          }
        } else if (_source82.is_Div) {
          return false;
        } else if (_source82.is_EuclidianDiv) {
          return false;
        } else if (_source82.is_Mod) {
          return false;
        } else if (_source82.is_EuclidianMod) {
          return false;
        } else if (_source82.is_Lt) {
          return false;
        } else if (_source82.is_LtChar) {
          return false;
        } else if (_source82.is_Plus) {
          return false;
        } else if (_source82.is_Minus) {
          return false;
        } else if (_source82.is_Times) {
          return false;
        } else if (_source82.is_BitwiseAnd) {
          return false;
        } else if (_source82.is_BitwiseOr) {
          return false;
        } else if (_source82.is_BitwiseXor) {
          return false;
        } else if (_source82.is_BitwiseShiftRight) {
          return false;
        } else if (_source82.is_BitwiseShiftLeft) {
          return false;
        } else if (_source82.is_And) {
          return false;
        } else if (_source82.is_Or) {
          return false;
        } else if (_source82.is_In) {
          return false;
        } else if (_source82.is_SeqProperPrefix) {
          return false;
        } else if (_source82.is_SeqPrefix) {
          return false;
        } else if (_source82.is_SetMerge) {
          return false;
        } else if (_source82.is_SetSubtraction) {
          return false;
        } else if (_source82.is_SetIntersection) {
          return false;
        } else if (_source82.is_Subset) {
          return false;
        } else if (_source82.is_ProperSubset) {
          return false;
        } else if (_source82.is_SetDisjoint) {
          return false;
        } else if (_source82.is_MapMerge) {
          return false;
        } else if (_source82.is_MapSubtraction) {
          return false;
        } else if (_source82.is_MultisetMerge) {
          return false;
        } else if (_source82.is_MultisetSubtraction) {
          return false;
        } else if (_source82.is_MultisetIntersection) {
          return false;
        } else if (_source82.is_Submultiset) {
          return false;
        } else if (_source82.is_ProperSubmultiset) {
          return false;
        } else if (_source82.is_MultisetDisjoint) {
          return false;
        } else if (_source82.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2374___mcc_h16 = _source82.dtor_Passthrough_a0;
          return false;
        }
      }))(_2359_op);
      DCOMP._IOwnership _2375_expectedLeftOwnership;
      _2375_expectedLeftOwnership = ((_2363_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_2367_becomesRightCallsLeft) || (_2371_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _2376_expectedRightOwnership;
      _2376_expectedRightOwnership = (((_2363_becomesLeftCallsRight) || (_2371_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_2367_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _2377_left;
      DCOMP._IOwnership _2378___v57;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2379_recIdentsL;
      RAST._IExpr _out189;
      DCOMP._IOwnership _out190;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
      (this).GenExpr(_2360_lExpr, selfIdent, @params, _2375_expectedLeftOwnership, out _out189, out _out190, out _out191);
      _2377_left = _out189;
      _2378___v57 = _out190;
      _2379_recIdentsL = _out191;
      RAST._IExpr _2380_right;
      DCOMP._IOwnership _2381___v58;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2382_recIdentsR;
      RAST._IExpr _out192;
      DCOMP._IOwnership _out193;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
      (this).GenExpr(_2361_rExpr, selfIdent, @params, _2376_expectedRightOwnership, out _out192, out _out193, out _out194);
      _2380_right = _out192;
      _2381___v58 = _out193;
      _2382_recIdentsR = _out194;
      DAST._IBinOp _source83 = _2359_op;
      if (_source83.is_Eq) {
        bool _2383___mcc_h18 = _source83.dtor_referential;
        bool _2384___mcc_h19 = _source83.dtor_nullable;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source84 = _2359_op;
            if (_source84.is_Eq) {
              bool _2385___mcc_h24 = _source84.dtor_referential;
              bool _2386___mcc_h25 = _source84.dtor_nullable;
              bool _2387_nullable = _2386___mcc_h25;
              bool _2388_referential = _2385___mcc_h24;
              {
                if (_2388_referential) {
                  if (_2387_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source84.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source84.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2389___mcc_h26 = _source84.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2390_op = _2389___mcc_h26;
              {
                r = RAST.Expr.create_BinaryOp(_2390_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_Div) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source85 = _2359_op;
            if (_source85.is_Eq) {
              bool _2391___mcc_h27 = _source85.dtor_referential;
              bool _2392___mcc_h28 = _source85.dtor_nullable;
              bool _2393_nullable = _2392___mcc_h28;
              bool _2394_referential = _2391___mcc_h27;
              {
                if (_2394_referential) {
                  if (_2393_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source85.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source85.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2395___mcc_h29 = _source85.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2396_op = _2395___mcc_h29;
              {
                r = RAST.Expr.create_BinaryOp(_2396_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_EuclidianDiv) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source86 = _2359_op;
            if (_source86.is_Eq) {
              bool _2397___mcc_h30 = _source86.dtor_referential;
              bool _2398___mcc_h31 = _source86.dtor_nullable;
              bool _2399_nullable = _2398___mcc_h31;
              bool _2400_referential = _2397___mcc_h30;
              {
                if (_2400_referential) {
                  if (_2399_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source86.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source86.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2401___mcc_h32 = _source86.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2402_op = _2401___mcc_h32;
              {
                r = RAST.Expr.create_BinaryOp(_2402_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_Mod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source87 = _2359_op;
            if (_source87.is_Eq) {
              bool _2403___mcc_h33 = _source87.dtor_referential;
              bool _2404___mcc_h34 = _source87.dtor_nullable;
              bool _2405_nullable = _2404___mcc_h34;
              bool _2406_referential = _2403___mcc_h33;
              {
                if (_2406_referential) {
                  if (_2405_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source87.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source87.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2407___mcc_h35 = _source87.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2408_op = _2407___mcc_h35;
              {
                r = RAST.Expr.create_BinaryOp(_2408_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_EuclidianMod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source88 = _2359_op;
            if (_source88.is_Eq) {
              bool _2409___mcc_h36 = _source88.dtor_referential;
              bool _2410___mcc_h37 = _source88.dtor_nullable;
              bool _2411_nullable = _2410___mcc_h37;
              bool _2412_referential = _2409___mcc_h36;
              {
                if (_2412_referential) {
                  if (_2411_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source88.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source88.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2413___mcc_h38 = _source88.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2414_op = _2413___mcc_h38;
              {
                r = RAST.Expr.create_BinaryOp(_2414_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_Lt) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source89 = _2359_op;
            if (_source89.is_Eq) {
              bool _2415___mcc_h39 = _source89.dtor_referential;
              bool _2416___mcc_h40 = _source89.dtor_nullable;
              bool _2417_nullable = _2416___mcc_h40;
              bool _2418_referential = _2415___mcc_h39;
              {
                if (_2418_referential) {
                  if (_2417_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source89.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source89.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2419___mcc_h41 = _source89.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2420_op = _2419___mcc_h41;
              {
                r = RAST.Expr.create_BinaryOp(_2420_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_LtChar) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source90 = _2359_op;
            if (_source90.is_Eq) {
              bool _2421___mcc_h42 = _source90.dtor_referential;
              bool _2422___mcc_h43 = _source90.dtor_nullable;
              bool _2423_nullable = _2422___mcc_h43;
              bool _2424_referential = _2421___mcc_h42;
              {
                if (_2424_referential) {
                  if (_2423_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source90.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source90.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2425___mcc_h44 = _source90.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2426_op = _2425___mcc_h44;
              {
                r = RAST.Expr.create_BinaryOp(_2426_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_Plus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source91 = _2359_op;
            if (_source91.is_Eq) {
              bool _2427___mcc_h45 = _source91.dtor_referential;
              bool _2428___mcc_h46 = _source91.dtor_nullable;
              bool _2429_nullable = _2428___mcc_h46;
              bool _2430_referential = _2427___mcc_h45;
              {
                if (_2430_referential) {
                  if (_2429_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source91.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source91.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2431___mcc_h47 = _source91.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2432_op = _2431___mcc_h47;
              {
                r = RAST.Expr.create_BinaryOp(_2432_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_Minus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source92 = _2359_op;
            if (_source92.is_Eq) {
              bool _2433___mcc_h48 = _source92.dtor_referential;
              bool _2434___mcc_h49 = _source92.dtor_nullable;
              bool _2435_nullable = _2434___mcc_h49;
              bool _2436_referential = _2433___mcc_h48;
              {
                if (_2436_referential) {
                  if (_2435_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source92.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source92.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2437___mcc_h50 = _source92.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2438_op = _2437___mcc_h50;
              {
                r = RAST.Expr.create_BinaryOp(_2438_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_Times) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source93 = _2359_op;
            if (_source93.is_Eq) {
              bool _2439___mcc_h51 = _source93.dtor_referential;
              bool _2440___mcc_h52 = _source93.dtor_nullable;
              bool _2441_nullable = _2440___mcc_h52;
              bool _2442_referential = _2439___mcc_h51;
              {
                if (_2442_referential) {
                  if (_2441_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source93.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source93.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2443___mcc_h53 = _source93.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2444_op = _2443___mcc_h53;
              {
                r = RAST.Expr.create_BinaryOp(_2444_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_BitwiseAnd) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source94 = _2359_op;
            if (_source94.is_Eq) {
              bool _2445___mcc_h54 = _source94.dtor_referential;
              bool _2446___mcc_h55 = _source94.dtor_nullable;
              bool _2447_nullable = _2446___mcc_h55;
              bool _2448_referential = _2445___mcc_h54;
              {
                if (_2448_referential) {
                  if (_2447_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source94.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source94.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2449___mcc_h56 = _source94.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2450_op = _2449___mcc_h56;
              {
                r = RAST.Expr.create_BinaryOp(_2450_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_BitwiseOr) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source95 = _2359_op;
            if (_source95.is_Eq) {
              bool _2451___mcc_h57 = _source95.dtor_referential;
              bool _2452___mcc_h58 = _source95.dtor_nullable;
              bool _2453_nullable = _2452___mcc_h58;
              bool _2454_referential = _2451___mcc_h57;
              {
                if (_2454_referential) {
                  if (_2453_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source95.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source95.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2455___mcc_h59 = _source95.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2456_op = _2455___mcc_h59;
              {
                r = RAST.Expr.create_BinaryOp(_2456_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_BitwiseXor) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source96 = _2359_op;
            if (_source96.is_Eq) {
              bool _2457___mcc_h60 = _source96.dtor_referential;
              bool _2458___mcc_h61 = _source96.dtor_nullable;
              bool _2459_nullable = _2458___mcc_h61;
              bool _2460_referential = _2457___mcc_h60;
              {
                if (_2460_referential) {
                  if (_2459_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source96.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source96.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2461___mcc_h62 = _source96.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2462_op = _2461___mcc_h62;
              {
                r = RAST.Expr.create_BinaryOp(_2462_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_BitwiseShiftRight) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source97 = _2359_op;
            if (_source97.is_Eq) {
              bool _2463___mcc_h63 = _source97.dtor_referential;
              bool _2464___mcc_h64 = _source97.dtor_nullable;
              bool _2465_nullable = _2464___mcc_h64;
              bool _2466_referential = _2463___mcc_h63;
              {
                if (_2466_referential) {
                  if (_2465_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source97.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source97.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2467___mcc_h65 = _source97.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2468_op = _2467___mcc_h65;
              {
                r = RAST.Expr.create_BinaryOp(_2468_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_BitwiseShiftLeft) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source98 = _2359_op;
            if (_source98.is_Eq) {
              bool _2469___mcc_h66 = _source98.dtor_referential;
              bool _2470___mcc_h67 = _source98.dtor_nullable;
              bool _2471_nullable = _2470___mcc_h67;
              bool _2472_referential = _2469___mcc_h66;
              {
                if (_2472_referential) {
                  if (_2471_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source98.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source98.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2473___mcc_h68 = _source98.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2474_op = _2473___mcc_h68;
              {
                r = RAST.Expr.create_BinaryOp(_2474_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_And) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source99 = _2359_op;
            if (_source99.is_Eq) {
              bool _2475___mcc_h69 = _source99.dtor_referential;
              bool _2476___mcc_h70 = _source99.dtor_nullable;
              bool _2477_nullable = _2476___mcc_h70;
              bool _2478_referential = _2475___mcc_h69;
              {
                if (_2478_referential) {
                  if (_2477_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source99.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source99.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2479___mcc_h71 = _source99.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2480_op = _2479___mcc_h71;
              {
                r = RAST.Expr.create_BinaryOp(_2480_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_Or) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source100 = _2359_op;
            if (_source100.is_Eq) {
              bool _2481___mcc_h72 = _source100.dtor_referential;
              bool _2482___mcc_h73 = _source100.dtor_nullable;
              bool _2483_nullable = _2482___mcc_h73;
              bool _2484_referential = _2481___mcc_h72;
              {
                if (_2484_referential) {
                  if (_2483_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source100.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source100.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2485___mcc_h74 = _source100.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2486_op = _2485___mcc_h74;
              {
                r = RAST.Expr.create_BinaryOp(_2486_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      } else if (_source83.is_In) {
        {
          r = ((_2380_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_2377_left);
        }
      } else if (_source83.is_SeqProperPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2377_left, _2380_right, _2362_format);
      } else if (_source83.is_SeqPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2377_left, _2380_right, _2362_format);
      } else if (_source83.is_SetMerge) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2380_right);
        }
      } else if (_source83.is_SetSubtraction) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2380_right);
        }
      } else if (_source83.is_SetIntersection) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2380_right);
        }
      } else if (_source83.is_Subset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2377_left, _2380_right, _2362_format);
        }
      } else if (_source83.is_ProperSubset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2377_left, _2380_right, _2362_format);
        }
      } else if (_source83.is_SetDisjoint) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2380_right);
        }
      } else if (_source83.is_MapMerge) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2380_right);
        }
      } else if (_source83.is_MapSubtraction) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2380_right);
        }
      } else if (_source83.is_MultisetMerge) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2380_right);
        }
      } else if (_source83.is_MultisetSubtraction) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2380_right);
        }
      } else if (_source83.is_MultisetIntersection) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2380_right);
        }
      } else if (_source83.is_Submultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2377_left, _2380_right, _2362_format);
        }
      } else if (_source83.is_ProperSubmultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2377_left, _2380_right, _2362_format);
        }
      } else if (_source83.is_MultisetDisjoint) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2380_right);
        }
      } else if (_source83.is_Concat) {
        {
          r = ((_2377_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_2380_right);
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _2487___mcc_h22 = _source83.dtor_Passthrough_a0;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2359_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2359_op), _2377_left, _2380_right, _2362_format);
          } else {
            DAST._IBinOp _source101 = _2359_op;
            if (_source101.is_Eq) {
              bool _2488___mcc_h75 = _source101.dtor_referential;
              bool _2489___mcc_h76 = _source101.dtor_nullable;
              bool _2490_nullable = _2489___mcc_h76;
              bool _2491_referential = _2488___mcc_h75;
              {
                if (_2491_referential) {
                  if (_2490_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2377_left, _2380_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source101.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else if (_source101.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2377_left, _2380_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2492___mcc_h77 = _source101.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2493_op = _2492___mcc_h77;
              {
                r = RAST.Expr.create_BinaryOp(_2493_op, _2377_left, _2380_right, _2362_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out195;
      DCOMP._IOwnership _out196;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out195, out _out196);
      r = _out195;
      resultingOwnership = _out196;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2379_recIdentsL, _2382_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs50 = e;
      DAST._IExpression _2494_expr = _let_tmp_rhs50.dtor_value;
      DAST._IType _2495_fromTpe = _let_tmp_rhs50.dtor_from;
      DAST._IType _2496_toTpe = _let_tmp_rhs50.dtor_typ;
      RAST._IExpr _2497_recursiveGen;
      DCOMP._IOwnership _2498_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2499_recIdents;
      RAST._IExpr _out197;
      DCOMP._IOwnership _out198;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out199;
      (this).GenExpr(_2494_expr, selfIdent, @params, expectedOwnership, out _out197, out _out198, out _out199);
      _2497_recursiveGen = _out197;
      _2498_recOwned = _out198;
      _2499_recIdents = _out199;
      r = _2497_recursiveGen;
      if (object.Equals(_2498_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out200;
      DCOMP._IOwnership _out201;
      DCOMP.COMP.FromOwnership(r, _2498_recOwned, expectedOwnership, out _out200, out _out201);
      r = _out200;
      resultingOwnership = _out201;
      readIdents = _2499_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs51 = e;
      DAST._IExpression _2500_expr = _let_tmp_rhs51.dtor_value;
      DAST._IType _2501_fromTpe = _let_tmp_rhs51.dtor_from;
      DAST._IType _2502_toTpe = _let_tmp_rhs51.dtor_typ;
      RAST._IExpr _2503_recursiveGen;
      DCOMP._IOwnership _2504_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2505_recIdents;
      RAST._IExpr _out202;
      DCOMP._IOwnership _out203;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
      (this).GenExpr(_2500_expr, selfIdent, @params, expectedOwnership, out _out202, out _out203, out _out204);
      _2503_recursiveGen = _out202;
      _2504_recOwned = _out203;
      _2505_recIdents = _out204;
      r = _2503_recursiveGen;
      if (object.Equals(_2504_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out205;
      DCOMP._IOwnership _out206;
      DCOMP.COMP.FromOwnership(r, _2504_recOwned, expectedOwnership, out _out205, out _out206);
      r = _out205;
      resultingOwnership = _out206;
      readIdents = _2505_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs52 = e;
      DAST._IExpression _2506_expr = _let_tmp_rhs52.dtor_value;
      DAST._IType _2507_fromTpe = _let_tmp_rhs52.dtor_from;
      DAST._IType _2508_toTpe = _let_tmp_rhs52.dtor_typ;
      DAST._IType _let_tmp_rhs53 = _2508_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2509___v60 = _let_tmp_rhs53.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _2510___v61 = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs54 = _let_tmp_rhs53.dtor_resolved;
      DAST._IType _2511_b = _let_tmp_rhs54.dtor_baseType;
      DAST._INewtypeRange _2512_range = _let_tmp_rhs54.dtor_range;
      bool _2513_erase = _let_tmp_rhs54.dtor_erase;
      if (object.Equals(_2507_fromTpe, _2511_b)) {
        RAST._IExpr _2514_recursiveGen;
        DCOMP._IOwnership _2515_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2516_recIdents;
        RAST._IExpr _out207;
        DCOMP._IOwnership _out208;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
        (this).GenExpr(_2506_expr, selfIdent, @params, expectedOwnership, out _out207, out _out208, out _out209);
        _2514_recursiveGen = _out207;
        _2515_recOwned = _out208;
        _2516_recIdents = _out209;
        Std.Wrappers._IOption<RAST._IType> _2517_potentialRhsType;
        _2517_potentialRhsType = DCOMP.COMP.NewtypeToRustType(_2511_b, _2512_range);
        Std.Wrappers._IOption<RAST._IType> _source102 = _2517_potentialRhsType;
        if (_source102.is_None) {
          if (_2513_erase) {
            r = _2514_recursiveGen;
          } else {
            RAST._IType _2518_rhsType;
            RAST._IType _out210;
            _out210 = (this).GenType(_2508_toTpe, true, false);
            _2518_rhsType = _out210;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_2518_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_2514_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out211;
          DCOMP._IOwnership _out212;
          DCOMP.COMP.FromOwnership(r, _2515_recOwned, expectedOwnership, out _out211, out _out212);
          r = _out211;
          resultingOwnership = _out212;
        } else {
          RAST._IType _2519___mcc_h0 = _source102.dtor_value;
          RAST._IType _2520_v = _2519___mcc_h0;
          r = RAST.Expr.create_ConversionNum(_2520_v, _2514_recursiveGen);
          RAST._IExpr _out213;
          DCOMP._IOwnership _out214;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out213, out _out214);
          r = _out213;
          resultingOwnership = _out214;
        }
        readIdents = _2516_recIdents;
      } else {
        RAST._IExpr _out215;
        DCOMP._IOwnership _out216;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out217;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_2506_expr, _2507_fromTpe, _2511_b), _2511_b, _2508_toTpe), selfIdent, @params, expectedOwnership, out _out215, out _out216, out _out217);
        r = _out215;
        resultingOwnership = _out216;
        readIdents = _out217;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _2521_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _2522_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _2523_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _2522_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2524___v62 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _2525___v63 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _2526_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _2527_range = _let_tmp_rhs57.dtor_range;
      bool _2528_erase = _let_tmp_rhs57.dtor_erase;
      if (object.Equals(_2526_b, _2523_toTpe)) {
        RAST._IExpr _2529_recursiveGen;
        DCOMP._IOwnership _2530_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2531_recIdents;
        RAST._IExpr _out218;
        DCOMP._IOwnership _out219;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out220;
        (this).GenExpr(_2521_expr, selfIdent, @params, expectedOwnership, out _out218, out _out219, out _out220);
        _2529_recursiveGen = _out218;
        _2530_recOwned = _out219;
        _2531_recIdents = _out220;
        if (_2528_erase) {
          r = _2529_recursiveGen;
        } else {
          r = (_2529_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
        }
        RAST._IExpr _out221;
        DCOMP._IOwnership _out222;
        DCOMP.COMP.FromOwnership(r, _2530_recOwned, expectedOwnership, out _out221, out _out222);
        r = _out221;
        resultingOwnership = _out222;
        readIdents = _2531_recIdents;
      } else {
        RAST._IExpr _out223;
        DCOMP._IOwnership _out224;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_2521_expr, _2522_fromTpe, _2526_b), _2526_b, _2523_toTpe), selfIdent, @params, expectedOwnership, out _out223, out _out224, out _out225);
        r = _out223;
        resultingOwnership = _out224;
        readIdents = _out225;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _2532_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _2533_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _2534_toTpe = _let_tmp_rhs58.dtor_typ;
      RAST._IExpr _2535_recursiveGen;
      DCOMP._IOwnership _2536_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2537_recIdents;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_2532_expr, selfIdent, @params, expectedOwnership, out _out226, out _out227, out _out228);
      _2535_recursiveGen = _out226;
      _2536_recOwned = _out227;
      _2537_recIdents = _out228;
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_2535_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)")));
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out229, out _out230);
      r = _out229;
      resultingOwnership = _out230;
      readIdents = _2537_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs59 = e;
      DAST._IExpression _2538_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _2539_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _2540_toTpe = _let_tmp_rhs59.dtor_typ;
      if (object.Equals(_2539_fromTpe, _2540_toTpe)) {
        RAST._IExpr _2541_recursiveGen;
        DCOMP._IOwnership _2542_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2543_recIdents;
        RAST._IExpr _out231;
        DCOMP._IOwnership _out232;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out233;
        (this).GenExpr(_2538_expr, selfIdent, @params, expectedOwnership, out _out231, out _out232, out _out233);
        _2541_recursiveGen = _out231;
        _2542_recOwned = _out232;
        _2543_recIdents = _out233;
        r = _2541_recursiveGen;
        RAST._IExpr _out234;
        DCOMP._IOwnership _out235;
        DCOMP.COMP.FromOwnership(r, _2542_recOwned, expectedOwnership, out _out234, out _out235);
        r = _out234;
        resultingOwnership = _out235;
        readIdents = _2543_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source103 = _System.Tuple2<DAST._IType, DAST._IType>.create(_2539_fromTpe, _2540_toTpe);
        DAST._IType _2544___mcc_h0 = _source103.dtor__0;
        DAST._IType _2545___mcc_h1 = _source103.dtor__1;
        DAST._IType _source104 = _2544___mcc_h0;
        if (_source104.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2546___mcc_h4 = _source104.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _2547___mcc_h5 = _source104.dtor_typeArgs;
          DAST._IResolvedType _2548___mcc_h6 = _source104.dtor_resolved;
          DAST._IResolvedType _source105 = _2548___mcc_h6;
          if (_source105.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2549___mcc_h16 = _source105.dtor_path;
            DAST._IType _source106 = _2545___mcc_h1;
            if (_source106.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2550___mcc_h20 = _source106.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2551___mcc_h21 = _source106.dtor_typeArgs;
              DAST._IResolvedType _2552___mcc_h22 = _source106.dtor_resolved;
              DAST._IResolvedType _source107 = _2552___mcc_h22;
              if (_source107.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2553___mcc_h26 = _source107.dtor_path;
                {
                  RAST._IExpr _out236;
                  DCOMP._IOwnership _out237;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out238;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out236, out _out237, out _out238);
                  r = _out236;
                  resultingOwnership = _out237;
                  readIdents = _out238;
                }
              } else if (_source107.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2554___mcc_h28 = _source107.dtor_path;
                {
                  RAST._IExpr _out239;
                  DCOMP._IOwnership _out240;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out239, out _out240, out _out241);
                  r = _out239;
                  resultingOwnership = _out240;
                  readIdents = _out241;
                }
              } else {
                DAST._IType _2555___mcc_h30 = _source107.dtor_baseType;
                DAST._INewtypeRange _2556___mcc_h31 = _source107.dtor_range;
                bool _2557___mcc_h32 = _source107.dtor_erase;
                bool _2558_erase = _2557___mcc_h32;
                DAST._INewtypeRange _2559_range = _2556___mcc_h31;
                DAST._IType _2560_b = _2555___mcc_h30;
                {
                  RAST._IExpr _out242;
                  DCOMP._IOwnership _out243;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
                  (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out242, out _out243, out _out244);
                  r = _out242;
                  resultingOwnership = _out243;
                  readIdents = _out244;
                }
              }
            } else if (_source106.is_Nullable) {
              DAST._IType _2561___mcc_h36 = _source106.dtor_Nullable_a0;
              {
                RAST._IExpr _out245;
                DCOMP._IOwnership _out246;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out247;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out245, out _out246, out _out247);
                r = _out245;
                resultingOwnership = _out246;
                readIdents = _out247;
              }
            } else if (_source106.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2562___mcc_h38 = _source106.dtor_Tuple_a0;
              {
                RAST._IExpr _out248;
                DCOMP._IOwnership _out249;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out248, out _out249, out _out250);
                r = _out248;
                resultingOwnership = _out249;
                readIdents = _out250;
              }
            } else if (_source106.is_Array) {
              DAST._IType _2563___mcc_h40 = _source106.dtor_element;
              BigInteger _2564___mcc_h41 = _source106.dtor_dims;
              {
                RAST._IExpr _out251;
                DCOMP._IOwnership _out252;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out251, out _out252, out _out253);
                r = _out251;
                resultingOwnership = _out252;
                readIdents = _out253;
              }
            } else if (_source106.is_Seq) {
              DAST._IType _2565___mcc_h44 = _source106.dtor_element;
              {
                RAST._IExpr _out254;
                DCOMP._IOwnership _out255;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out256;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out254, out _out255, out _out256);
                r = _out254;
                resultingOwnership = _out255;
                readIdents = _out256;
              }
            } else if (_source106.is_Set) {
              DAST._IType _2566___mcc_h46 = _source106.dtor_element;
              {
                RAST._IExpr _out257;
                DCOMP._IOwnership _out258;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out259;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out257, out _out258, out _out259);
                r = _out257;
                resultingOwnership = _out258;
                readIdents = _out259;
              }
            } else if (_source106.is_Multiset) {
              DAST._IType _2567___mcc_h48 = _source106.dtor_element;
              {
                RAST._IExpr _out260;
                DCOMP._IOwnership _out261;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out260, out _out261, out _out262);
                r = _out260;
                resultingOwnership = _out261;
                readIdents = _out262;
              }
            } else if (_source106.is_Map) {
              DAST._IType _2568___mcc_h50 = _source106.dtor_key;
              DAST._IType _2569___mcc_h51 = _source106.dtor_value;
              {
                RAST._IExpr _out263;
                DCOMP._IOwnership _out264;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out263, out _out264, out _out265);
                r = _out263;
                resultingOwnership = _out264;
                readIdents = _out265;
              }
            } else if (_source106.is_SetBuilder) {
              DAST._IType _2570___mcc_h54 = _source106.dtor_element;
              {
                RAST._IExpr _out266;
                DCOMP._IOwnership _out267;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out268;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out266, out _out267, out _out268);
                r = _out266;
                resultingOwnership = _out267;
                readIdents = _out268;
              }
            } else if (_source106.is_MapBuilder) {
              DAST._IType _2571___mcc_h56 = _source106.dtor_key;
              DAST._IType _2572___mcc_h57 = _source106.dtor_value;
              {
                RAST._IExpr _out269;
                DCOMP._IOwnership _out270;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out269, out _out270, out _out271);
                r = _out269;
                resultingOwnership = _out270;
                readIdents = _out271;
              }
            } else if (_source106.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2573___mcc_h60 = _source106.dtor_args;
              DAST._IType _2574___mcc_h61 = _source106.dtor_result;
              {
                RAST._IExpr _out272;
                DCOMP._IOwnership _out273;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out272, out _out273, out _out274);
                r = _out272;
                resultingOwnership = _out273;
                readIdents = _out274;
              }
            } else if (_source106.is_Primitive) {
              DAST._IPrimitive _2575___mcc_h64 = _source106.dtor_Primitive_a0;
              {
                RAST._IExpr _out275;
                DCOMP._IOwnership _out276;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out275, out _out276, out _out277);
                r = _out275;
                resultingOwnership = _out276;
                readIdents = _out277;
              }
            } else if (_source106.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2576___mcc_h66 = _source106.dtor_Passthrough_a0;
              {
                RAST._IExpr _out278;
                DCOMP._IOwnership _out279;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out278, out _out279, out _out280);
                r = _out278;
                resultingOwnership = _out279;
                readIdents = _out280;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2577___mcc_h68 = _source106.dtor_TypeArg_a0;
              {
                RAST._IExpr _out281;
                DCOMP._IOwnership _out282;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out283;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out281, out _out282, out _out283);
                r = _out281;
                resultingOwnership = _out282;
                readIdents = _out283;
              }
            }
          } else if (_source105.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2578___mcc_h70 = _source105.dtor_path;
            DAST._IType _source108 = _2545___mcc_h1;
            if (_source108.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2579___mcc_h74 = _source108.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2580___mcc_h75 = _source108.dtor_typeArgs;
              DAST._IResolvedType _2581___mcc_h76 = _source108.dtor_resolved;
              DAST._IResolvedType _source109 = _2581___mcc_h76;
              if (_source109.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2582___mcc_h80 = _source109.dtor_path;
                {
                  RAST._IExpr _out284;
                  DCOMP._IOwnership _out285;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out284, out _out285, out _out286);
                  r = _out284;
                  resultingOwnership = _out285;
                  readIdents = _out286;
                }
              } else if (_source109.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2583___mcc_h82 = _source109.dtor_path;
                {
                  RAST._IExpr _out287;
                  DCOMP._IOwnership _out288;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out289;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out287, out _out288, out _out289);
                  r = _out287;
                  resultingOwnership = _out288;
                  readIdents = _out289;
                }
              } else {
                DAST._IType _2584___mcc_h84 = _source109.dtor_baseType;
                DAST._INewtypeRange _2585___mcc_h85 = _source109.dtor_range;
                bool _2586___mcc_h86 = _source109.dtor_erase;
                bool _2587_erase = _2586___mcc_h86;
                DAST._INewtypeRange _2588_range = _2585___mcc_h85;
                DAST._IType _2589_b = _2584___mcc_h84;
                {
                  RAST._IExpr _out290;
                  DCOMP._IOwnership _out291;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out292;
                  (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out290, out _out291, out _out292);
                  r = _out290;
                  resultingOwnership = _out291;
                  readIdents = _out292;
                }
              }
            } else if (_source108.is_Nullable) {
              DAST._IType _2590___mcc_h90 = _source108.dtor_Nullable_a0;
              {
                RAST._IExpr _out293;
                DCOMP._IOwnership _out294;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out295;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out293, out _out294, out _out295);
                r = _out293;
                resultingOwnership = _out294;
                readIdents = _out295;
              }
            } else if (_source108.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2591___mcc_h92 = _source108.dtor_Tuple_a0;
              {
                RAST._IExpr _out296;
                DCOMP._IOwnership _out297;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out296, out _out297, out _out298);
                r = _out296;
                resultingOwnership = _out297;
                readIdents = _out298;
              }
            } else if (_source108.is_Array) {
              DAST._IType _2592___mcc_h94 = _source108.dtor_element;
              BigInteger _2593___mcc_h95 = _source108.dtor_dims;
              {
                RAST._IExpr _out299;
                DCOMP._IOwnership _out300;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out299, out _out300, out _out301);
                r = _out299;
                resultingOwnership = _out300;
                readIdents = _out301;
              }
            } else if (_source108.is_Seq) {
              DAST._IType _2594___mcc_h98 = _source108.dtor_element;
              {
                RAST._IExpr _out302;
                DCOMP._IOwnership _out303;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out302, out _out303, out _out304);
                r = _out302;
                resultingOwnership = _out303;
                readIdents = _out304;
              }
            } else if (_source108.is_Set) {
              DAST._IType _2595___mcc_h100 = _source108.dtor_element;
              {
                RAST._IExpr _out305;
                DCOMP._IOwnership _out306;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out305, out _out306, out _out307);
                r = _out305;
                resultingOwnership = _out306;
                readIdents = _out307;
              }
            } else if (_source108.is_Multiset) {
              DAST._IType _2596___mcc_h102 = _source108.dtor_element;
              {
                RAST._IExpr _out308;
                DCOMP._IOwnership _out309;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out310;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out308, out _out309, out _out310);
                r = _out308;
                resultingOwnership = _out309;
                readIdents = _out310;
              }
            } else if (_source108.is_Map) {
              DAST._IType _2597___mcc_h104 = _source108.dtor_key;
              DAST._IType _2598___mcc_h105 = _source108.dtor_value;
              {
                RAST._IExpr _out311;
                DCOMP._IOwnership _out312;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out313;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out311, out _out312, out _out313);
                r = _out311;
                resultingOwnership = _out312;
                readIdents = _out313;
              }
            } else if (_source108.is_SetBuilder) {
              DAST._IType _2599___mcc_h108 = _source108.dtor_element;
              {
                RAST._IExpr _out314;
                DCOMP._IOwnership _out315;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out314, out _out315, out _out316);
                r = _out314;
                resultingOwnership = _out315;
                readIdents = _out316;
              }
            } else if (_source108.is_MapBuilder) {
              DAST._IType _2600___mcc_h110 = _source108.dtor_key;
              DAST._IType _2601___mcc_h111 = _source108.dtor_value;
              {
                RAST._IExpr _out317;
                DCOMP._IOwnership _out318;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out317, out _out318, out _out319);
                r = _out317;
                resultingOwnership = _out318;
                readIdents = _out319;
              }
            } else if (_source108.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2602___mcc_h114 = _source108.dtor_args;
              DAST._IType _2603___mcc_h115 = _source108.dtor_result;
              {
                RAST._IExpr _out320;
                DCOMP._IOwnership _out321;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out320, out _out321, out _out322);
                r = _out320;
                resultingOwnership = _out321;
                readIdents = _out322;
              }
            } else if (_source108.is_Primitive) {
              DAST._IPrimitive _2604___mcc_h118 = _source108.dtor_Primitive_a0;
              {
                RAST._IExpr _out323;
                DCOMP._IOwnership _out324;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out325;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out323, out _out324, out _out325);
                r = _out323;
                resultingOwnership = _out324;
                readIdents = _out325;
              }
            } else if (_source108.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2605___mcc_h120 = _source108.dtor_Passthrough_a0;
              {
                RAST._IExpr _out326;
                DCOMP._IOwnership _out327;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out328;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out326, out _out327, out _out328);
                r = _out326;
                resultingOwnership = _out327;
                readIdents = _out328;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2606___mcc_h122 = _source108.dtor_TypeArg_a0;
              {
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out329, out _out330, out _out331);
                r = _out329;
                resultingOwnership = _out330;
                readIdents = _out331;
              }
            }
          } else {
            DAST._IType _2607___mcc_h124 = _source105.dtor_baseType;
            DAST._INewtypeRange _2608___mcc_h125 = _source105.dtor_range;
            bool _2609___mcc_h126 = _source105.dtor_erase;
            DAST._IType _source110 = _2545___mcc_h1;
            if (_source110.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2610___mcc_h136 = _source110.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2611___mcc_h137 = _source110.dtor_typeArgs;
              DAST._IResolvedType _2612___mcc_h138 = _source110.dtor_resolved;
              DAST._IResolvedType _source111 = _2612___mcc_h138;
              if (_source111.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2613___mcc_h145 = _source111.dtor_path;
                bool _2614_erase = _2609___mcc_h126;
                DAST._INewtypeRange _2615_range = _2608___mcc_h125;
                DAST._IType _2616_b = _2607___mcc_h124;
                {
                  RAST._IExpr _out332;
                  DCOMP._IOwnership _out333;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                  (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out332, out _out333, out _out334);
                  r = _out332;
                  resultingOwnership = _out333;
                  readIdents = _out334;
                }
              } else if (_source111.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2617___mcc_h148 = _source111.dtor_path;
                bool _2618_erase = _2609___mcc_h126;
                DAST._INewtypeRange _2619_range = _2608___mcc_h125;
                DAST._IType _2620_b = _2607___mcc_h124;
                {
                  RAST._IExpr _out335;
                  DCOMP._IOwnership _out336;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out337;
                  (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out335, out _out336, out _out337);
                  r = _out335;
                  resultingOwnership = _out336;
                  readIdents = _out337;
                }
              } else {
                DAST._IType _2621___mcc_h151 = _source111.dtor_baseType;
                DAST._INewtypeRange _2622___mcc_h152 = _source111.dtor_range;
                bool _2623___mcc_h153 = _source111.dtor_erase;
                bool _2624_erase = _2623___mcc_h153;
                DAST._INewtypeRange _2625_range = _2622___mcc_h152;
                DAST._IType _2626_b = _2621___mcc_h151;
                {
                  RAST._IExpr _out338;
                  DCOMP._IOwnership _out339;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out340;
                  (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out338, out _out339, out _out340);
                  r = _out338;
                  resultingOwnership = _out339;
                  readIdents = _out340;
                }
              }
            } else if (_source110.is_Nullable) {
              DAST._IType _2627___mcc_h160 = _source110.dtor_Nullable_a0;
              {
                RAST._IExpr _out341;
                DCOMP._IOwnership _out342;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out341, out _out342, out _out343);
                r = _out341;
                resultingOwnership = _out342;
                readIdents = _out343;
              }
            } else if (_source110.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2628___mcc_h163 = _source110.dtor_Tuple_a0;
              bool _2629_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2630_range = _2608___mcc_h125;
              DAST._IType _2631_b = _2607___mcc_h124;
              {
                RAST._IExpr _out344;
                DCOMP._IOwnership _out345;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out346;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out344, out _out345, out _out346);
                r = _out344;
                resultingOwnership = _out345;
                readIdents = _out346;
              }
            } else if (_source110.is_Array) {
              DAST._IType _2632___mcc_h166 = _source110.dtor_element;
              BigInteger _2633___mcc_h167 = _source110.dtor_dims;
              bool _2634_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2635_range = _2608___mcc_h125;
              DAST._IType _2636_b = _2607___mcc_h124;
              {
                RAST._IExpr _out347;
                DCOMP._IOwnership _out348;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out347, out _out348, out _out349);
                r = _out347;
                resultingOwnership = _out348;
                readIdents = _out349;
              }
            } else if (_source110.is_Seq) {
              DAST._IType _2637___mcc_h172 = _source110.dtor_element;
              bool _2638_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2639_range = _2608___mcc_h125;
              DAST._IType _2640_b = _2607___mcc_h124;
              {
                RAST._IExpr _out350;
                DCOMP._IOwnership _out351;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out350, out _out351, out _out352);
                r = _out350;
                resultingOwnership = _out351;
                readIdents = _out352;
              }
            } else if (_source110.is_Set) {
              DAST._IType _2641___mcc_h175 = _source110.dtor_element;
              bool _2642_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2643_range = _2608___mcc_h125;
              DAST._IType _2644_b = _2607___mcc_h124;
              {
                RAST._IExpr _out353;
                DCOMP._IOwnership _out354;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out353, out _out354, out _out355);
                r = _out353;
                resultingOwnership = _out354;
                readIdents = _out355;
              }
            } else if (_source110.is_Multiset) {
              DAST._IType _2645___mcc_h178 = _source110.dtor_element;
              bool _2646_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2647_range = _2608___mcc_h125;
              DAST._IType _2648_b = _2607___mcc_h124;
              {
                RAST._IExpr _out356;
                DCOMP._IOwnership _out357;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out356, out _out357, out _out358);
                r = _out356;
                resultingOwnership = _out357;
                readIdents = _out358;
              }
            } else if (_source110.is_Map) {
              DAST._IType _2649___mcc_h181 = _source110.dtor_key;
              DAST._IType _2650___mcc_h182 = _source110.dtor_value;
              bool _2651_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2652_range = _2608___mcc_h125;
              DAST._IType _2653_b = _2607___mcc_h124;
              {
                RAST._IExpr _out359;
                DCOMP._IOwnership _out360;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out359, out _out360, out _out361);
                r = _out359;
                resultingOwnership = _out360;
                readIdents = _out361;
              }
            } else if (_source110.is_SetBuilder) {
              DAST._IType _2654___mcc_h187 = _source110.dtor_element;
              bool _2655_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2656_range = _2608___mcc_h125;
              DAST._IType _2657_b = _2607___mcc_h124;
              {
                RAST._IExpr _out362;
                DCOMP._IOwnership _out363;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out362, out _out363, out _out364);
                r = _out362;
                resultingOwnership = _out363;
                readIdents = _out364;
              }
            } else if (_source110.is_MapBuilder) {
              DAST._IType _2658___mcc_h190 = _source110.dtor_key;
              DAST._IType _2659___mcc_h191 = _source110.dtor_value;
              bool _2660_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2661_range = _2608___mcc_h125;
              DAST._IType _2662_b = _2607___mcc_h124;
              {
                RAST._IExpr _out365;
                DCOMP._IOwnership _out366;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out365, out _out366, out _out367);
                r = _out365;
                resultingOwnership = _out366;
                readIdents = _out367;
              }
            } else if (_source110.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2663___mcc_h196 = _source110.dtor_args;
              DAST._IType _2664___mcc_h197 = _source110.dtor_result;
              bool _2665_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2666_range = _2608___mcc_h125;
              DAST._IType _2667_b = _2607___mcc_h124;
              {
                RAST._IExpr _out368;
                DCOMP._IOwnership _out369;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out370;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out368, out _out369, out _out370);
                r = _out368;
                resultingOwnership = _out369;
                readIdents = _out370;
              }
            } else if (_source110.is_Primitive) {
              DAST._IPrimitive _2668___mcc_h202 = _source110.dtor_Primitive_a0;
              bool _2669_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2670_range = _2608___mcc_h125;
              DAST._IType _2671_b = _2607___mcc_h124;
              {
                RAST._IExpr _out371;
                DCOMP._IOwnership _out372;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out371, out _out372, out _out373);
                r = _out371;
                resultingOwnership = _out372;
                readIdents = _out373;
              }
            } else if (_source110.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2672___mcc_h205 = _source110.dtor_Passthrough_a0;
              bool _2673_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2674_range = _2608___mcc_h125;
              DAST._IType _2675_b = _2607___mcc_h124;
              {
                RAST._IExpr _out374;
                DCOMP._IOwnership _out375;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out374, out _out375, out _out376);
                r = _out374;
                resultingOwnership = _out375;
                readIdents = _out376;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2676___mcc_h208 = _source110.dtor_TypeArg_a0;
              bool _2677_erase = _2609___mcc_h126;
              DAST._INewtypeRange _2678_range = _2608___mcc_h125;
              DAST._IType _2679_b = _2607___mcc_h124;
              {
                RAST._IExpr _out377;
                DCOMP._IOwnership _out378;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out377, out _out378, out _out379);
                r = _out377;
                resultingOwnership = _out378;
                readIdents = _out379;
              }
            }
          }
        } else if (_source104.is_Nullable) {
          DAST._IType _2680___mcc_h211 = _source104.dtor_Nullable_a0;
          DAST._IType _source112 = _2545___mcc_h1;
          if (_source112.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2681___mcc_h215 = _source112.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2682___mcc_h216 = _source112.dtor_typeArgs;
            DAST._IResolvedType _2683___mcc_h217 = _source112.dtor_resolved;
            DAST._IResolvedType _source113 = _2683___mcc_h217;
            if (_source113.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2684___mcc_h224 = _source113.dtor_path;
              {
                RAST._IExpr _out380;
                DCOMP._IOwnership _out381;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
                (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out380, out _out381, out _out382);
                r = _out380;
                resultingOwnership = _out381;
                readIdents = _out382;
              }
            } else if (_source113.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2685___mcc_h227 = _source113.dtor_path;
              {
                RAST._IExpr _out383;
                DCOMP._IOwnership _out384;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
                (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out383, out _out384, out _out385);
                r = _out383;
                resultingOwnership = _out384;
                readIdents = _out385;
              }
            } else {
              DAST._IType _2686___mcc_h230 = _source113.dtor_baseType;
              DAST._INewtypeRange _2687___mcc_h231 = _source113.dtor_range;
              bool _2688___mcc_h232 = _source113.dtor_erase;
              {
                RAST._IExpr _out386;
                DCOMP._IOwnership _out387;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out388;
                (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out386, out _out387, out _out388);
                r = _out386;
                resultingOwnership = _out387;
                readIdents = _out388;
              }
            }
          } else if (_source112.is_Nullable) {
            DAST._IType _2689___mcc_h239 = _source112.dtor_Nullable_a0;
            {
              RAST._IExpr _out389;
              DCOMP._IOwnership _out390;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out389, out _out390, out _out391);
              r = _out389;
              resultingOwnership = _out390;
              readIdents = _out391;
            }
          } else if (_source112.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2690___mcc_h242 = _source112.dtor_Tuple_a0;
            {
              RAST._IExpr _out392;
              DCOMP._IOwnership _out393;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out394;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out392, out _out393, out _out394);
              r = _out392;
              resultingOwnership = _out393;
              readIdents = _out394;
            }
          } else if (_source112.is_Array) {
            DAST._IType _2691___mcc_h245 = _source112.dtor_element;
            BigInteger _2692___mcc_h246 = _source112.dtor_dims;
            {
              RAST._IExpr _out395;
              DCOMP._IOwnership _out396;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out397;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out395, out _out396, out _out397);
              r = _out395;
              resultingOwnership = _out396;
              readIdents = _out397;
            }
          } else if (_source112.is_Seq) {
            DAST._IType _2693___mcc_h251 = _source112.dtor_element;
            {
              RAST._IExpr _out398;
              DCOMP._IOwnership _out399;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out398, out _out399, out _out400);
              r = _out398;
              resultingOwnership = _out399;
              readIdents = _out400;
            }
          } else if (_source112.is_Set) {
            DAST._IType _2694___mcc_h254 = _source112.dtor_element;
            {
              RAST._IExpr _out401;
              DCOMP._IOwnership _out402;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out401, out _out402, out _out403);
              r = _out401;
              resultingOwnership = _out402;
              readIdents = _out403;
            }
          } else if (_source112.is_Multiset) {
            DAST._IType _2695___mcc_h257 = _source112.dtor_element;
            {
              RAST._IExpr _out404;
              DCOMP._IOwnership _out405;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out404, out _out405, out _out406);
              r = _out404;
              resultingOwnership = _out405;
              readIdents = _out406;
            }
          } else if (_source112.is_Map) {
            DAST._IType _2696___mcc_h260 = _source112.dtor_key;
            DAST._IType _2697___mcc_h261 = _source112.dtor_value;
            {
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out407, out _out408, out _out409);
              r = _out407;
              resultingOwnership = _out408;
              readIdents = _out409;
            }
          } else if (_source112.is_SetBuilder) {
            DAST._IType _2698___mcc_h266 = _source112.dtor_element;
            {
              RAST._IExpr _out410;
              DCOMP._IOwnership _out411;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out410, out _out411, out _out412);
              r = _out410;
              resultingOwnership = _out411;
              readIdents = _out412;
            }
          } else if (_source112.is_MapBuilder) {
            DAST._IType _2699___mcc_h269 = _source112.dtor_key;
            DAST._IType _2700___mcc_h270 = _source112.dtor_value;
            {
              RAST._IExpr _out413;
              DCOMP._IOwnership _out414;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out413, out _out414, out _out415);
              r = _out413;
              resultingOwnership = _out414;
              readIdents = _out415;
            }
          } else if (_source112.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2701___mcc_h275 = _source112.dtor_args;
            DAST._IType _2702___mcc_h276 = _source112.dtor_result;
            {
              RAST._IExpr _out416;
              DCOMP._IOwnership _out417;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out418;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out416, out _out417, out _out418);
              r = _out416;
              resultingOwnership = _out417;
              readIdents = _out418;
            }
          } else if (_source112.is_Primitive) {
            DAST._IPrimitive _2703___mcc_h281 = _source112.dtor_Primitive_a0;
            {
              RAST._IExpr _out419;
              DCOMP._IOwnership _out420;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out419, out _out420, out _out421);
              r = _out419;
              resultingOwnership = _out420;
              readIdents = _out421;
            }
          } else if (_source112.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2704___mcc_h284 = _source112.dtor_Passthrough_a0;
            {
              RAST._IExpr _out422;
              DCOMP._IOwnership _out423;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out422, out _out423, out _out424);
              r = _out422;
              resultingOwnership = _out423;
              readIdents = _out424;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2705___mcc_h287 = _source112.dtor_TypeArg_a0;
            {
              RAST._IExpr _out425;
              DCOMP._IOwnership _out426;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out425, out _out426, out _out427);
              r = _out425;
              resultingOwnership = _out426;
              readIdents = _out427;
            }
          }
        } else if (_source104.is_Tuple) {
          Dafny.ISequence<DAST._IType> _2706___mcc_h290 = _source104.dtor_Tuple_a0;
          DAST._IType _source114 = _2545___mcc_h1;
          if (_source114.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2707___mcc_h294 = _source114.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2708___mcc_h295 = _source114.dtor_typeArgs;
            DAST._IResolvedType _2709___mcc_h296 = _source114.dtor_resolved;
            DAST._IResolvedType _source115 = _2709___mcc_h296;
            if (_source115.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2710___mcc_h300 = _source115.dtor_path;
              {
                RAST._IExpr _out428;
                DCOMP._IOwnership _out429;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out428, out _out429, out _out430);
                r = _out428;
                resultingOwnership = _out429;
                readIdents = _out430;
              }
            } else if (_source115.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2711___mcc_h302 = _source115.dtor_path;
              {
                RAST._IExpr _out431;
                DCOMP._IOwnership _out432;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out433;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out431, out _out432, out _out433);
                r = _out431;
                resultingOwnership = _out432;
                readIdents = _out433;
              }
            } else {
              DAST._IType _2712___mcc_h304 = _source115.dtor_baseType;
              DAST._INewtypeRange _2713___mcc_h305 = _source115.dtor_range;
              bool _2714___mcc_h306 = _source115.dtor_erase;
              bool _2715_erase = _2714___mcc_h306;
              DAST._INewtypeRange _2716_range = _2713___mcc_h305;
              DAST._IType _2717_b = _2712___mcc_h304;
              {
                RAST._IExpr _out434;
                DCOMP._IOwnership _out435;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out434, out _out435, out _out436);
                r = _out434;
                resultingOwnership = _out435;
                readIdents = _out436;
              }
            }
          } else if (_source114.is_Nullable) {
            DAST._IType _2718___mcc_h310 = _source114.dtor_Nullable_a0;
            {
              RAST._IExpr _out437;
              DCOMP._IOwnership _out438;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out437, out _out438, out _out439);
              r = _out437;
              resultingOwnership = _out438;
              readIdents = _out439;
            }
          } else if (_source114.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2719___mcc_h312 = _source114.dtor_Tuple_a0;
            {
              RAST._IExpr _out440;
              DCOMP._IOwnership _out441;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out440, out _out441, out _out442);
              r = _out440;
              resultingOwnership = _out441;
              readIdents = _out442;
            }
          } else if (_source114.is_Array) {
            DAST._IType _2720___mcc_h314 = _source114.dtor_element;
            BigInteger _2721___mcc_h315 = _source114.dtor_dims;
            {
              RAST._IExpr _out443;
              DCOMP._IOwnership _out444;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out443, out _out444, out _out445);
              r = _out443;
              resultingOwnership = _out444;
              readIdents = _out445;
            }
          } else if (_source114.is_Seq) {
            DAST._IType _2722___mcc_h318 = _source114.dtor_element;
            {
              RAST._IExpr _out446;
              DCOMP._IOwnership _out447;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out446, out _out447, out _out448);
              r = _out446;
              resultingOwnership = _out447;
              readIdents = _out448;
            }
          } else if (_source114.is_Set) {
            DAST._IType _2723___mcc_h320 = _source114.dtor_element;
            {
              RAST._IExpr _out449;
              DCOMP._IOwnership _out450;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out449, out _out450, out _out451);
              r = _out449;
              resultingOwnership = _out450;
              readIdents = _out451;
            }
          } else if (_source114.is_Multiset) {
            DAST._IType _2724___mcc_h322 = _source114.dtor_element;
            {
              RAST._IExpr _out452;
              DCOMP._IOwnership _out453;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out452, out _out453, out _out454);
              r = _out452;
              resultingOwnership = _out453;
              readIdents = _out454;
            }
          } else if (_source114.is_Map) {
            DAST._IType _2725___mcc_h324 = _source114.dtor_key;
            DAST._IType _2726___mcc_h325 = _source114.dtor_value;
            {
              RAST._IExpr _out455;
              DCOMP._IOwnership _out456;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out455, out _out456, out _out457);
              r = _out455;
              resultingOwnership = _out456;
              readIdents = _out457;
            }
          } else if (_source114.is_SetBuilder) {
            DAST._IType _2727___mcc_h328 = _source114.dtor_element;
            {
              RAST._IExpr _out458;
              DCOMP._IOwnership _out459;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out458, out _out459, out _out460);
              r = _out458;
              resultingOwnership = _out459;
              readIdents = _out460;
            }
          } else if (_source114.is_MapBuilder) {
            DAST._IType _2728___mcc_h330 = _source114.dtor_key;
            DAST._IType _2729___mcc_h331 = _source114.dtor_value;
            {
              RAST._IExpr _out461;
              DCOMP._IOwnership _out462;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out463;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out461, out _out462, out _out463);
              r = _out461;
              resultingOwnership = _out462;
              readIdents = _out463;
            }
          } else if (_source114.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2730___mcc_h334 = _source114.dtor_args;
            DAST._IType _2731___mcc_h335 = _source114.dtor_result;
            {
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out464, out _out465, out _out466);
              r = _out464;
              resultingOwnership = _out465;
              readIdents = _out466;
            }
          } else if (_source114.is_Primitive) {
            DAST._IPrimitive _2732___mcc_h338 = _source114.dtor_Primitive_a0;
            {
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out467, out _out468, out _out469);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _out469;
            }
          } else if (_source114.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2733___mcc_h340 = _source114.dtor_Passthrough_a0;
            {
              RAST._IExpr _out470;
              DCOMP._IOwnership _out471;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out470, out _out471, out _out472);
              r = _out470;
              resultingOwnership = _out471;
              readIdents = _out472;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2734___mcc_h342 = _source114.dtor_TypeArg_a0;
            {
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out473, out _out474, out _out475);
              r = _out473;
              resultingOwnership = _out474;
              readIdents = _out475;
            }
          }
        } else if (_source104.is_Array) {
          DAST._IType _2735___mcc_h344 = _source104.dtor_element;
          BigInteger _2736___mcc_h345 = _source104.dtor_dims;
          DAST._IType _source116 = _2545___mcc_h1;
          if (_source116.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2737___mcc_h352 = _source116.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2738___mcc_h353 = _source116.dtor_typeArgs;
            DAST._IResolvedType _2739___mcc_h354 = _source116.dtor_resolved;
            DAST._IResolvedType _source117 = _2739___mcc_h354;
            if (_source117.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2740___mcc_h358 = _source117.dtor_path;
              {
                RAST._IExpr _out476;
                DCOMP._IOwnership _out477;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out478;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out476, out _out477, out _out478);
                r = _out476;
                resultingOwnership = _out477;
                readIdents = _out478;
              }
            } else if (_source117.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2741___mcc_h360 = _source117.dtor_path;
              {
                RAST._IExpr _out479;
                DCOMP._IOwnership _out480;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out479, out _out480, out _out481);
                r = _out479;
                resultingOwnership = _out480;
                readIdents = _out481;
              }
            } else {
              DAST._IType _2742___mcc_h362 = _source117.dtor_baseType;
              DAST._INewtypeRange _2743___mcc_h363 = _source117.dtor_range;
              bool _2744___mcc_h364 = _source117.dtor_erase;
              bool _2745_erase = _2744___mcc_h364;
              DAST._INewtypeRange _2746_range = _2743___mcc_h363;
              DAST._IType _2747_b = _2742___mcc_h362;
              {
                RAST._IExpr _out482;
                DCOMP._IOwnership _out483;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out482, out _out483, out _out484);
                r = _out482;
                resultingOwnership = _out483;
                readIdents = _out484;
              }
            }
          } else if (_source116.is_Nullable) {
            DAST._IType _2748___mcc_h368 = _source116.dtor_Nullable_a0;
            {
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out485, out _out486, out _out487);
              r = _out485;
              resultingOwnership = _out486;
              readIdents = _out487;
            }
          } else if (_source116.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2749___mcc_h370 = _source116.dtor_Tuple_a0;
            {
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out488, out _out489, out _out490);
              r = _out488;
              resultingOwnership = _out489;
              readIdents = _out490;
            }
          } else if (_source116.is_Array) {
            DAST._IType _2750___mcc_h372 = _source116.dtor_element;
            BigInteger _2751___mcc_h373 = _source116.dtor_dims;
            {
              RAST._IExpr _out491;
              DCOMP._IOwnership _out492;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out491, out _out492, out _out493);
              r = _out491;
              resultingOwnership = _out492;
              readIdents = _out493;
            }
          } else if (_source116.is_Seq) {
            DAST._IType _2752___mcc_h376 = _source116.dtor_element;
            {
              RAST._IExpr _out494;
              DCOMP._IOwnership _out495;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out494, out _out495, out _out496);
              r = _out494;
              resultingOwnership = _out495;
              readIdents = _out496;
            }
          } else if (_source116.is_Set) {
            DAST._IType _2753___mcc_h378 = _source116.dtor_element;
            {
              RAST._IExpr _out497;
              DCOMP._IOwnership _out498;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out497, out _out498, out _out499);
              r = _out497;
              resultingOwnership = _out498;
              readIdents = _out499;
            }
          } else if (_source116.is_Multiset) {
            DAST._IType _2754___mcc_h380 = _source116.dtor_element;
            {
              RAST._IExpr _out500;
              DCOMP._IOwnership _out501;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out502;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out500, out _out501, out _out502);
              r = _out500;
              resultingOwnership = _out501;
              readIdents = _out502;
            }
          } else if (_source116.is_Map) {
            DAST._IType _2755___mcc_h382 = _source116.dtor_key;
            DAST._IType _2756___mcc_h383 = _source116.dtor_value;
            {
              RAST._IExpr _out503;
              DCOMP._IOwnership _out504;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out503, out _out504, out _out505);
              r = _out503;
              resultingOwnership = _out504;
              readIdents = _out505;
            }
          } else if (_source116.is_SetBuilder) {
            DAST._IType _2757___mcc_h386 = _source116.dtor_element;
            {
              RAST._IExpr _out506;
              DCOMP._IOwnership _out507;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out506, out _out507, out _out508);
              r = _out506;
              resultingOwnership = _out507;
              readIdents = _out508;
            }
          } else if (_source116.is_MapBuilder) {
            DAST._IType _2758___mcc_h388 = _source116.dtor_key;
            DAST._IType _2759___mcc_h389 = _source116.dtor_value;
            {
              RAST._IExpr _out509;
              DCOMP._IOwnership _out510;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out509, out _out510, out _out511);
              r = _out509;
              resultingOwnership = _out510;
              readIdents = _out511;
            }
          } else if (_source116.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2760___mcc_h392 = _source116.dtor_args;
            DAST._IType _2761___mcc_h393 = _source116.dtor_result;
            {
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out512, out _out513, out _out514);
              r = _out512;
              resultingOwnership = _out513;
              readIdents = _out514;
            }
          } else if (_source116.is_Primitive) {
            DAST._IPrimitive _2762___mcc_h396 = _source116.dtor_Primitive_a0;
            {
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out515, out _out516, out _out517);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _out517;
            }
          } else if (_source116.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2763___mcc_h398 = _source116.dtor_Passthrough_a0;
            {
              RAST._IExpr _out518;
              DCOMP._IOwnership _out519;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out520;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out518, out _out519, out _out520);
              r = _out518;
              resultingOwnership = _out519;
              readIdents = _out520;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2764___mcc_h400 = _source116.dtor_TypeArg_a0;
            {
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out523;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out521, out _out522, out _out523);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _out523;
            }
          }
        } else if (_source104.is_Seq) {
          DAST._IType _2765___mcc_h402 = _source104.dtor_element;
          DAST._IType _source118 = _2545___mcc_h1;
          if (_source118.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2766___mcc_h406 = _source118.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2767___mcc_h407 = _source118.dtor_typeArgs;
            DAST._IResolvedType _2768___mcc_h408 = _source118.dtor_resolved;
            DAST._IResolvedType _source119 = _2768___mcc_h408;
            if (_source119.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2769___mcc_h412 = _source119.dtor_path;
              {
                RAST._IExpr _out524;
                DCOMP._IOwnership _out525;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out526;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out524, out _out525, out _out526);
                r = _out524;
                resultingOwnership = _out525;
                readIdents = _out526;
              }
            } else if (_source119.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2770___mcc_h414 = _source119.dtor_path;
              {
                RAST._IExpr _out527;
                DCOMP._IOwnership _out528;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out527, out _out528, out _out529);
                r = _out527;
                resultingOwnership = _out528;
                readIdents = _out529;
              }
            } else {
              DAST._IType _2771___mcc_h416 = _source119.dtor_baseType;
              DAST._INewtypeRange _2772___mcc_h417 = _source119.dtor_range;
              bool _2773___mcc_h418 = _source119.dtor_erase;
              bool _2774_erase = _2773___mcc_h418;
              DAST._INewtypeRange _2775_range = _2772___mcc_h417;
              DAST._IType _2776_b = _2771___mcc_h416;
              {
                RAST._IExpr _out530;
                DCOMP._IOwnership _out531;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out532;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out530, out _out531, out _out532);
                r = _out530;
                resultingOwnership = _out531;
                readIdents = _out532;
              }
            }
          } else if (_source118.is_Nullable) {
            DAST._IType _2777___mcc_h422 = _source118.dtor_Nullable_a0;
            {
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out533, out _out534, out _out535);
              r = _out533;
              resultingOwnership = _out534;
              readIdents = _out535;
            }
          } else if (_source118.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2778___mcc_h424 = _source118.dtor_Tuple_a0;
            {
              RAST._IExpr _out536;
              DCOMP._IOwnership _out537;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out536, out _out537, out _out538);
              r = _out536;
              resultingOwnership = _out537;
              readIdents = _out538;
            }
          } else if (_source118.is_Array) {
            DAST._IType _2779___mcc_h426 = _source118.dtor_element;
            BigInteger _2780___mcc_h427 = _source118.dtor_dims;
            {
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out539, out _out540, out _out541);
              r = _out539;
              resultingOwnership = _out540;
              readIdents = _out541;
            }
          } else if (_source118.is_Seq) {
            DAST._IType _2781___mcc_h430 = _source118.dtor_element;
            {
              RAST._IExpr _out542;
              DCOMP._IOwnership _out543;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out542, out _out543, out _out544);
              r = _out542;
              resultingOwnership = _out543;
              readIdents = _out544;
            }
          } else if (_source118.is_Set) {
            DAST._IType _2782___mcc_h432 = _source118.dtor_element;
            {
              RAST._IExpr _out545;
              DCOMP._IOwnership _out546;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out545, out _out546, out _out547);
              r = _out545;
              resultingOwnership = _out546;
              readIdents = _out547;
            }
          } else if (_source118.is_Multiset) {
            DAST._IType _2783___mcc_h434 = _source118.dtor_element;
            {
              RAST._IExpr _out548;
              DCOMP._IOwnership _out549;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out548, out _out549, out _out550);
              r = _out548;
              resultingOwnership = _out549;
              readIdents = _out550;
            }
          } else if (_source118.is_Map) {
            DAST._IType _2784___mcc_h436 = _source118.dtor_key;
            DAST._IType _2785___mcc_h437 = _source118.dtor_value;
            {
              RAST._IExpr _out551;
              DCOMP._IOwnership _out552;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out551, out _out552, out _out553);
              r = _out551;
              resultingOwnership = _out552;
              readIdents = _out553;
            }
          } else if (_source118.is_SetBuilder) {
            DAST._IType _2786___mcc_h440 = _source118.dtor_element;
            {
              RAST._IExpr _out554;
              DCOMP._IOwnership _out555;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out554, out _out555, out _out556);
              r = _out554;
              resultingOwnership = _out555;
              readIdents = _out556;
            }
          } else if (_source118.is_MapBuilder) {
            DAST._IType _2787___mcc_h442 = _source118.dtor_key;
            DAST._IType _2788___mcc_h443 = _source118.dtor_value;
            {
              RAST._IExpr _out557;
              DCOMP._IOwnership _out558;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out557, out _out558, out _out559);
              r = _out557;
              resultingOwnership = _out558;
              readIdents = _out559;
            }
          } else if (_source118.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2789___mcc_h446 = _source118.dtor_args;
            DAST._IType _2790___mcc_h447 = _source118.dtor_result;
            {
              RAST._IExpr _out560;
              DCOMP._IOwnership _out561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out560, out _out561, out _out562);
              r = _out560;
              resultingOwnership = _out561;
              readIdents = _out562;
            }
          } else if (_source118.is_Primitive) {
            DAST._IPrimitive _2791___mcc_h450 = _source118.dtor_Primitive_a0;
            {
              RAST._IExpr _out563;
              DCOMP._IOwnership _out564;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out563, out _out564, out _out565);
              r = _out563;
              resultingOwnership = _out564;
              readIdents = _out565;
            }
          } else if (_source118.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2792___mcc_h452 = _source118.dtor_Passthrough_a0;
            {
              RAST._IExpr _out566;
              DCOMP._IOwnership _out567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out566, out _out567, out _out568);
              r = _out566;
              resultingOwnership = _out567;
              readIdents = _out568;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2793___mcc_h454 = _source118.dtor_TypeArg_a0;
            {
              RAST._IExpr _out569;
              DCOMP._IOwnership _out570;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out569, out _out570, out _out571);
              r = _out569;
              resultingOwnership = _out570;
              readIdents = _out571;
            }
          }
        } else if (_source104.is_Set) {
          DAST._IType _2794___mcc_h456 = _source104.dtor_element;
          DAST._IType _source120 = _2545___mcc_h1;
          if (_source120.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2795___mcc_h460 = _source120.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2796___mcc_h461 = _source120.dtor_typeArgs;
            DAST._IResolvedType _2797___mcc_h462 = _source120.dtor_resolved;
            DAST._IResolvedType _source121 = _2797___mcc_h462;
            if (_source121.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2798___mcc_h466 = _source121.dtor_path;
              {
                RAST._IExpr _out572;
                DCOMP._IOwnership _out573;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out572, out _out573, out _out574);
                r = _out572;
                resultingOwnership = _out573;
                readIdents = _out574;
              }
            } else if (_source121.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2799___mcc_h468 = _source121.dtor_path;
              {
                RAST._IExpr _out575;
                DCOMP._IOwnership _out576;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out575, out _out576, out _out577);
                r = _out575;
                resultingOwnership = _out576;
                readIdents = _out577;
              }
            } else {
              DAST._IType _2800___mcc_h470 = _source121.dtor_baseType;
              DAST._INewtypeRange _2801___mcc_h471 = _source121.dtor_range;
              bool _2802___mcc_h472 = _source121.dtor_erase;
              bool _2803_erase = _2802___mcc_h472;
              DAST._INewtypeRange _2804_range = _2801___mcc_h471;
              DAST._IType _2805_b = _2800___mcc_h470;
              {
                RAST._IExpr _out578;
                DCOMP._IOwnership _out579;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out580;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out578, out _out579, out _out580);
                r = _out578;
                resultingOwnership = _out579;
                readIdents = _out580;
              }
            }
          } else if (_source120.is_Nullable) {
            DAST._IType _2806___mcc_h476 = _source120.dtor_Nullable_a0;
            {
              RAST._IExpr _out581;
              DCOMP._IOwnership _out582;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out583;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out581, out _out582, out _out583);
              r = _out581;
              resultingOwnership = _out582;
              readIdents = _out583;
            }
          } else if (_source120.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2807___mcc_h478 = _source120.dtor_Tuple_a0;
            {
              RAST._IExpr _out584;
              DCOMP._IOwnership _out585;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out584, out _out585, out _out586);
              r = _out584;
              resultingOwnership = _out585;
              readIdents = _out586;
            }
          } else if (_source120.is_Array) {
            DAST._IType _2808___mcc_h480 = _source120.dtor_element;
            BigInteger _2809___mcc_h481 = _source120.dtor_dims;
            {
              RAST._IExpr _out587;
              DCOMP._IOwnership _out588;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out587, out _out588, out _out589);
              r = _out587;
              resultingOwnership = _out588;
              readIdents = _out589;
            }
          } else if (_source120.is_Seq) {
            DAST._IType _2810___mcc_h484 = _source120.dtor_element;
            {
              RAST._IExpr _out590;
              DCOMP._IOwnership _out591;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out590, out _out591, out _out592);
              r = _out590;
              resultingOwnership = _out591;
              readIdents = _out592;
            }
          } else if (_source120.is_Set) {
            DAST._IType _2811___mcc_h486 = _source120.dtor_element;
            {
              RAST._IExpr _out593;
              DCOMP._IOwnership _out594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out595;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out593, out _out594, out _out595);
              r = _out593;
              resultingOwnership = _out594;
              readIdents = _out595;
            }
          } else if (_source120.is_Multiset) {
            DAST._IType _2812___mcc_h488 = _source120.dtor_element;
            {
              RAST._IExpr _out596;
              DCOMP._IOwnership _out597;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out596, out _out597, out _out598);
              r = _out596;
              resultingOwnership = _out597;
              readIdents = _out598;
            }
          } else if (_source120.is_Map) {
            DAST._IType _2813___mcc_h490 = _source120.dtor_key;
            DAST._IType _2814___mcc_h491 = _source120.dtor_value;
            {
              RAST._IExpr _out599;
              DCOMP._IOwnership _out600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out599, out _out600, out _out601);
              r = _out599;
              resultingOwnership = _out600;
              readIdents = _out601;
            }
          } else if (_source120.is_SetBuilder) {
            DAST._IType _2815___mcc_h494 = _source120.dtor_element;
            {
              RAST._IExpr _out602;
              DCOMP._IOwnership _out603;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out602, out _out603, out _out604);
              r = _out602;
              resultingOwnership = _out603;
              readIdents = _out604;
            }
          } else if (_source120.is_MapBuilder) {
            DAST._IType _2816___mcc_h496 = _source120.dtor_key;
            DAST._IType _2817___mcc_h497 = _source120.dtor_value;
            {
              RAST._IExpr _out605;
              DCOMP._IOwnership _out606;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out605, out _out606, out _out607);
              r = _out605;
              resultingOwnership = _out606;
              readIdents = _out607;
            }
          } else if (_source120.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2818___mcc_h500 = _source120.dtor_args;
            DAST._IType _2819___mcc_h501 = _source120.dtor_result;
            {
              RAST._IExpr _out608;
              DCOMP._IOwnership _out609;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out608, out _out609, out _out610);
              r = _out608;
              resultingOwnership = _out609;
              readIdents = _out610;
            }
          } else if (_source120.is_Primitive) {
            DAST._IPrimitive _2820___mcc_h504 = _source120.dtor_Primitive_a0;
            {
              RAST._IExpr _out611;
              DCOMP._IOwnership _out612;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out611, out _out612, out _out613);
              r = _out611;
              resultingOwnership = _out612;
              readIdents = _out613;
            }
          } else if (_source120.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2821___mcc_h506 = _source120.dtor_Passthrough_a0;
            {
              RAST._IExpr _out614;
              DCOMP._IOwnership _out615;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out616;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out614, out _out615, out _out616);
              r = _out614;
              resultingOwnership = _out615;
              readIdents = _out616;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2822___mcc_h508 = _source120.dtor_TypeArg_a0;
            {
              RAST._IExpr _out617;
              DCOMP._IOwnership _out618;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out617, out _out618, out _out619);
              r = _out617;
              resultingOwnership = _out618;
              readIdents = _out619;
            }
          }
        } else if (_source104.is_Multiset) {
          DAST._IType _2823___mcc_h510 = _source104.dtor_element;
          DAST._IType _source122 = _2545___mcc_h1;
          if (_source122.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2824___mcc_h514 = _source122.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2825___mcc_h515 = _source122.dtor_typeArgs;
            DAST._IResolvedType _2826___mcc_h516 = _source122.dtor_resolved;
            DAST._IResolvedType _source123 = _2826___mcc_h516;
            if (_source123.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2827___mcc_h520 = _source123.dtor_path;
              {
                RAST._IExpr _out620;
                DCOMP._IOwnership _out621;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out620, out _out621, out _out622);
                r = _out620;
                resultingOwnership = _out621;
                readIdents = _out622;
              }
            } else if (_source123.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2828___mcc_h522 = _source123.dtor_path;
              {
                RAST._IExpr _out623;
                DCOMP._IOwnership _out624;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out623, out _out624, out _out625);
                r = _out623;
                resultingOwnership = _out624;
                readIdents = _out625;
              }
            } else {
              DAST._IType _2829___mcc_h524 = _source123.dtor_baseType;
              DAST._INewtypeRange _2830___mcc_h525 = _source123.dtor_range;
              bool _2831___mcc_h526 = _source123.dtor_erase;
              bool _2832_erase = _2831___mcc_h526;
              DAST._INewtypeRange _2833_range = _2830___mcc_h525;
              DAST._IType _2834_b = _2829___mcc_h524;
              {
                RAST._IExpr _out626;
                DCOMP._IOwnership _out627;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out628;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out626, out _out627, out _out628);
                r = _out626;
                resultingOwnership = _out627;
                readIdents = _out628;
              }
            }
          } else if (_source122.is_Nullable) {
            DAST._IType _2835___mcc_h530 = _source122.dtor_Nullable_a0;
            {
              RAST._IExpr _out629;
              DCOMP._IOwnership _out630;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out631;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out629, out _out630, out _out631);
              r = _out629;
              resultingOwnership = _out630;
              readIdents = _out631;
            }
          } else if (_source122.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2836___mcc_h532 = _source122.dtor_Tuple_a0;
            {
              RAST._IExpr _out632;
              DCOMP._IOwnership _out633;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out632, out _out633, out _out634);
              r = _out632;
              resultingOwnership = _out633;
              readIdents = _out634;
            }
          } else if (_source122.is_Array) {
            DAST._IType _2837___mcc_h534 = _source122.dtor_element;
            BigInteger _2838___mcc_h535 = _source122.dtor_dims;
            {
              RAST._IExpr _out635;
              DCOMP._IOwnership _out636;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out635, out _out636, out _out637);
              r = _out635;
              resultingOwnership = _out636;
              readIdents = _out637;
            }
          } else if (_source122.is_Seq) {
            DAST._IType _2839___mcc_h538 = _source122.dtor_element;
            {
              RAST._IExpr _out638;
              DCOMP._IOwnership _out639;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out638, out _out639, out _out640);
              r = _out638;
              resultingOwnership = _out639;
              readIdents = _out640;
            }
          } else if (_source122.is_Set) {
            DAST._IType _2840___mcc_h540 = _source122.dtor_element;
            {
              RAST._IExpr _out641;
              DCOMP._IOwnership _out642;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out641, out _out642, out _out643);
              r = _out641;
              resultingOwnership = _out642;
              readIdents = _out643;
            }
          } else if (_source122.is_Multiset) {
            DAST._IType _2841___mcc_h542 = _source122.dtor_element;
            {
              RAST._IExpr _out644;
              DCOMP._IOwnership _out645;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out646;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out644, out _out645, out _out646);
              r = _out644;
              resultingOwnership = _out645;
              readIdents = _out646;
            }
          } else if (_source122.is_Map) {
            DAST._IType _2842___mcc_h544 = _source122.dtor_key;
            DAST._IType _2843___mcc_h545 = _source122.dtor_value;
            {
              RAST._IExpr _out647;
              DCOMP._IOwnership _out648;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out647, out _out648, out _out649);
              r = _out647;
              resultingOwnership = _out648;
              readIdents = _out649;
            }
          } else if (_source122.is_SetBuilder) {
            DAST._IType _2844___mcc_h548 = _source122.dtor_element;
            {
              RAST._IExpr _out650;
              DCOMP._IOwnership _out651;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out652;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out650, out _out651, out _out652);
              r = _out650;
              resultingOwnership = _out651;
              readIdents = _out652;
            }
          } else if (_source122.is_MapBuilder) {
            DAST._IType _2845___mcc_h550 = _source122.dtor_key;
            DAST._IType _2846___mcc_h551 = _source122.dtor_value;
            {
              RAST._IExpr _out653;
              DCOMP._IOwnership _out654;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out653, out _out654, out _out655);
              r = _out653;
              resultingOwnership = _out654;
              readIdents = _out655;
            }
          } else if (_source122.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2847___mcc_h554 = _source122.dtor_args;
            DAST._IType _2848___mcc_h555 = _source122.dtor_result;
            {
              RAST._IExpr _out656;
              DCOMP._IOwnership _out657;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out656, out _out657, out _out658);
              r = _out656;
              resultingOwnership = _out657;
              readIdents = _out658;
            }
          } else if (_source122.is_Primitive) {
            DAST._IPrimitive _2849___mcc_h558 = _source122.dtor_Primitive_a0;
            {
              RAST._IExpr _out659;
              DCOMP._IOwnership _out660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out659, out _out660, out _out661);
              r = _out659;
              resultingOwnership = _out660;
              readIdents = _out661;
            }
          } else if (_source122.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2850___mcc_h560 = _source122.dtor_Passthrough_a0;
            {
              RAST._IExpr _out662;
              DCOMP._IOwnership _out663;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out664;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out662, out _out663, out _out664);
              r = _out662;
              resultingOwnership = _out663;
              readIdents = _out664;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2851___mcc_h562 = _source122.dtor_TypeArg_a0;
            {
              RAST._IExpr _out665;
              DCOMP._IOwnership _out666;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out665, out _out666, out _out667);
              r = _out665;
              resultingOwnership = _out666;
              readIdents = _out667;
            }
          }
        } else if (_source104.is_Map) {
          DAST._IType _2852___mcc_h564 = _source104.dtor_key;
          DAST._IType _2853___mcc_h565 = _source104.dtor_value;
          DAST._IType _source124 = _2545___mcc_h1;
          if (_source124.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2854___mcc_h572 = _source124.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2855___mcc_h573 = _source124.dtor_typeArgs;
            DAST._IResolvedType _2856___mcc_h574 = _source124.dtor_resolved;
            DAST._IResolvedType _source125 = _2856___mcc_h574;
            if (_source125.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2857___mcc_h578 = _source125.dtor_path;
              {
                RAST._IExpr _out668;
                DCOMP._IOwnership _out669;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out670;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out668, out _out669, out _out670);
                r = _out668;
                resultingOwnership = _out669;
                readIdents = _out670;
              }
            } else if (_source125.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2858___mcc_h580 = _source125.dtor_path;
              {
                RAST._IExpr _out671;
                DCOMP._IOwnership _out672;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out673;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out671, out _out672, out _out673);
                r = _out671;
                resultingOwnership = _out672;
                readIdents = _out673;
              }
            } else {
              DAST._IType _2859___mcc_h582 = _source125.dtor_baseType;
              DAST._INewtypeRange _2860___mcc_h583 = _source125.dtor_range;
              bool _2861___mcc_h584 = _source125.dtor_erase;
              bool _2862_erase = _2861___mcc_h584;
              DAST._INewtypeRange _2863_range = _2860___mcc_h583;
              DAST._IType _2864_b = _2859___mcc_h582;
              {
                RAST._IExpr _out674;
                DCOMP._IOwnership _out675;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out676;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out674, out _out675, out _out676);
                r = _out674;
                resultingOwnership = _out675;
                readIdents = _out676;
              }
            }
          } else if (_source124.is_Nullable) {
            DAST._IType _2865___mcc_h588 = _source124.dtor_Nullable_a0;
            {
              RAST._IExpr _out677;
              DCOMP._IOwnership _out678;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out677, out _out678, out _out679);
              r = _out677;
              resultingOwnership = _out678;
              readIdents = _out679;
            }
          } else if (_source124.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2866___mcc_h590 = _source124.dtor_Tuple_a0;
            {
              RAST._IExpr _out680;
              DCOMP._IOwnership _out681;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out682;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out680, out _out681, out _out682);
              r = _out680;
              resultingOwnership = _out681;
              readIdents = _out682;
            }
          } else if (_source124.is_Array) {
            DAST._IType _2867___mcc_h592 = _source124.dtor_element;
            BigInteger _2868___mcc_h593 = _source124.dtor_dims;
            {
              RAST._IExpr _out683;
              DCOMP._IOwnership _out684;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out685;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out683, out _out684, out _out685);
              r = _out683;
              resultingOwnership = _out684;
              readIdents = _out685;
            }
          } else if (_source124.is_Seq) {
            DAST._IType _2869___mcc_h596 = _source124.dtor_element;
            {
              RAST._IExpr _out686;
              DCOMP._IOwnership _out687;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out688;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out686, out _out687, out _out688);
              r = _out686;
              resultingOwnership = _out687;
              readIdents = _out688;
            }
          } else if (_source124.is_Set) {
            DAST._IType _2870___mcc_h598 = _source124.dtor_element;
            {
              RAST._IExpr _out689;
              DCOMP._IOwnership _out690;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out689, out _out690, out _out691);
              r = _out689;
              resultingOwnership = _out690;
              readIdents = _out691;
            }
          } else if (_source124.is_Multiset) {
            DAST._IType _2871___mcc_h600 = _source124.dtor_element;
            {
              RAST._IExpr _out692;
              DCOMP._IOwnership _out693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out694;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out692, out _out693, out _out694);
              r = _out692;
              resultingOwnership = _out693;
              readIdents = _out694;
            }
          } else if (_source124.is_Map) {
            DAST._IType _2872___mcc_h602 = _source124.dtor_key;
            DAST._IType _2873___mcc_h603 = _source124.dtor_value;
            {
              RAST._IExpr _out695;
              DCOMP._IOwnership _out696;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out697;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out695, out _out696, out _out697);
              r = _out695;
              resultingOwnership = _out696;
              readIdents = _out697;
            }
          } else if (_source124.is_SetBuilder) {
            DAST._IType _2874___mcc_h606 = _source124.dtor_element;
            {
              RAST._IExpr _out698;
              DCOMP._IOwnership _out699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out698, out _out699, out _out700);
              r = _out698;
              resultingOwnership = _out699;
              readIdents = _out700;
            }
          } else if (_source124.is_MapBuilder) {
            DAST._IType _2875___mcc_h608 = _source124.dtor_key;
            DAST._IType _2876___mcc_h609 = _source124.dtor_value;
            {
              RAST._IExpr _out701;
              DCOMP._IOwnership _out702;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out703;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out701, out _out702, out _out703);
              r = _out701;
              resultingOwnership = _out702;
              readIdents = _out703;
            }
          } else if (_source124.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2877___mcc_h612 = _source124.dtor_args;
            DAST._IType _2878___mcc_h613 = _source124.dtor_result;
            {
              RAST._IExpr _out704;
              DCOMP._IOwnership _out705;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out706;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out704, out _out705, out _out706);
              r = _out704;
              resultingOwnership = _out705;
              readIdents = _out706;
            }
          } else if (_source124.is_Primitive) {
            DAST._IPrimitive _2879___mcc_h616 = _source124.dtor_Primitive_a0;
            {
              RAST._IExpr _out707;
              DCOMP._IOwnership _out708;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out709;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out707, out _out708, out _out709);
              r = _out707;
              resultingOwnership = _out708;
              readIdents = _out709;
            }
          } else if (_source124.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2880___mcc_h618 = _source124.dtor_Passthrough_a0;
            {
              RAST._IExpr _out710;
              DCOMP._IOwnership _out711;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out710, out _out711, out _out712);
              r = _out710;
              resultingOwnership = _out711;
              readIdents = _out712;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2881___mcc_h620 = _source124.dtor_TypeArg_a0;
            {
              RAST._IExpr _out713;
              DCOMP._IOwnership _out714;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out715;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out713, out _out714, out _out715);
              r = _out713;
              resultingOwnership = _out714;
              readIdents = _out715;
            }
          }
        } else if (_source104.is_SetBuilder) {
          DAST._IType _2882___mcc_h622 = _source104.dtor_element;
          DAST._IType _source126 = _2545___mcc_h1;
          if (_source126.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2883___mcc_h626 = _source126.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2884___mcc_h627 = _source126.dtor_typeArgs;
            DAST._IResolvedType _2885___mcc_h628 = _source126.dtor_resolved;
            DAST._IResolvedType _source127 = _2885___mcc_h628;
            if (_source127.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2886___mcc_h632 = _source127.dtor_path;
              {
                RAST._IExpr _out716;
                DCOMP._IOwnership _out717;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out718;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out716, out _out717, out _out718);
                r = _out716;
                resultingOwnership = _out717;
                readIdents = _out718;
              }
            } else if (_source127.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2887___mcc_h634 = _source127.dtor_path;
              {
                RAST._IExpr _out719;
                DCOMP._IOwnership _out720;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out721;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out719, out _out720, out _out721);
                r = _out719;
                resultingOwnership = _out720;
                readIdents = _out721;
              }
            } else {
              DAST._IType _2888___mcc_h636 = _source127.dtor_baseType;
              DAST._INewtypeRange _2889___mcc_h637 = _source127.dtor_range;
              bool _2890___mcc_h638 = _source127.dtor_erase;
              bool _2891_erase = _2890___mcc_h638;
              DAST._INewtypeRange _2892_range = _2889___mcc_h637;
              DAST._IType _2893_b = _2888___mcc_h636;
              {
                RAST._IExpr _out722;
                DCOMP._IOwnership _out723;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out724;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out722, out _out723, out _out724);
                r = _out722;
                resultingOwnership = _out723;
                readIdents = _out724;
              }
            }
          } else if (_source126.is_Nullable) {
            DAST._IType _2894___mcc_h642 = _source126.dtor_Nullable_a0;
            {
              RAST._IExpr _out725;
              DCOMP._IOwnership _out726;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out727;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out725, out _out726, out _out727);
              r = _out725;
              resultingOwnership = _out726;
              readIdents = _out727;
            }
          } else if (_source126.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2895___mcc_h644 = _source126.dtor_Tuple_a0;
            {
              RAST._IExpr _out728;
              DCOMP._IOwnership _out729;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out730;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out728, out _out729, out _out730);
              r = _out728;
              resultingOwnership = _out729;
              readIdents = _out730;
            }
          } else if (_source126.is_Array) {
            DAST._IType _2896___mcc_h646 = _source126.dtor_element;
            BigInteger _2897___mcc_h647 = _source126.dtor_dims;
            {
              RAST._IExpr _out731;
              DCOMP._IOwnership _out732;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out733;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out731, out _out732, out _out733);
              r = _out731;
              resultingOwnership = _out732;
              readIdents = _out733;
            }
          } else if (_source126.is_Seq) {
            DAST._IType _2898___mcc_h650 = _source126.dtor_element;
            {
              RAST._IExpr _out734;
              DCOMP._IOwnership _out735;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out734, out _out735, out _out736);
              r = _out734;
              resultingOwnership = _out735;
              readIdents = _out736;
            }
          } else if (_source126.is_Set) {
            DAST._IType _2899___mcc_h652 = _source126.dtor_element;
            {
              RAST._IExpr _out737;
              DCOMP._IOwnership _out738;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out739;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out737, out _out738, out _out739);
              r = _out737;
              resultingOwnership = _out738;
              readIdents = _out739;
            }
          } else if (_source126.is_Multiset) {
            DAST._IType _2900___mcc_h654 = _source126.dtor_element;
            {
              RAST._IExpr _out740;
              DCOMP._IOwnership _out741;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out742;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out740, out _out741, out _out742);
              r = _out740;
              resultingOwnership = _out741;
              readIdents = _out742;
            }
          } else if (_source126.is_Map) {
            DAST._IType _2901___mcc_h656 = _source126.dtor_key;
            DAST._IType _2902___mcc_h657 = _source126.dtor_value;
            {
              RAST._IExpr _out743;
              DCOMP._IOwnership _out744;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out745;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out743, out _out744, out _out745);
              r = _out743;
              resultingOwnership = _out744;
              readIdents = _out745;
            }
          } else if (_source126.is_SetBuilder) {
            DAST._IType _2903___mcc_h660 = _source126.dtor_element;
            {
              RAST._IExpr _out746;
              DCOMP._IOwnership _out747;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out746, out _out747, out _out748);
              r = _out746;
              resultingOwnership = _out747;
              readIdents = _out748;
            }
          } else if (_source126.is_MapBuilder) {
            DAST._IType _2904___mcc_h662 = _source126.dtor_key;
            DAST._IType _2905___mcc_h663 = _source126.dtor_value;
            {
              RAST._IExpr _out749;
              DCOMP._IOwnership _out750;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out751;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out749, out _out750, out _out751);
              r = _out749;
              resultingOwnership = _out750;
              readIdents = _out751;
            }
          } else if (_source126.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2906___mcc_h666 = _source126.dtor_args;
            DAST._IType _2907___mcc_h667 = _source126.dtor_result;
            {
              RAST._IExpr _out752;
              DCOMP._IOwnership _out753;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out754;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out752, out _out753, out _out754);
              r = _out752;
              resultingOwnership = _out753;
              readIdents = _out754;
            }
          } else if (_source126.is_Primitive) {
            DAST._IPrimitive _2908___mcc_h670 = _source126.dtor_Primitive_a0;
            {
              RAST._IExpr _out755;
              DCOMP._IOwnership _out756;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out757;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out755, out _out756, out _out757);
              r = _out755;
              resultingOwnership = _out756;
              readIdents = _out757;
            }
          } else if (_source126.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2909___mcc_h672 = _source126.dtor_Passthrough_a0;
            {
              RAST._IExpr _out758;
              DCOMP._IOwnership _out759;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out760;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out758, out _out759, out _out760);
              r = _out758;
              resultingOwnership = _out759;
              readIdents = _out760;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2910___mcc_h674 = _source126.dtor_TypeArg_a0;
            {
              RAST._IExpr _out761;
              DCOMP._IOwnership _out762;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out763;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out761, out _out762, out _out763);
              r = _out761;
              resultingOwnership = _out762;
              readIdents = _out763;
            }
          }
        } else if (_source104.is_MapBuilder) {
          DAST._IType _2911___mcc_h676 = _source104.dtor_key;
          DAST._IType _2912___mcc_h677 = _source104.dtor_value;
          DAST._IType _source128 = _2545___mcc_h1;
          if (_source128.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2913___mcc_h684 = _source128.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2914___mcc_h685 = _source128.dtor_typeArgs;
            DAST._IResolvedType _2915___mcc_h686 = _source128.dtor_resolved;
            DAST._IResolvedType _source129 = _2915___mcc_h686;
            if (_source129.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2916___mcc_h690 = _source129.dtor_path;
              {
                RAST._IExpr _out764;
                DCOMP._IOwnership _out765;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out766;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out764, out _out765, out _out766);
                r = _out764;
                resultingOwnership = _out765;
                readIdents = _out766;
              }
            } else if (_source129.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2917___mcc_h692 = _source129.dtor_path;
              {
                RAST._IExpr _out767;
                DCOMP._IOwnership _out768;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out767, out _out768, out _out769);
                r = _out767;
                resultingOwnership = _out768;
                readIdents = _out769;
              }
            } else {
              DAST._IType _2918___mcc_h694 = _source129.dtor_baseType;
              DAST._INewtypeRange _2919___mcc_h695 = _source129.dtor_range;
              bool _2920___mcc_h696 = _source129.dtor_erase;
              bool _2921_erase = _2920___mcc_h696;
              DAST._INewtypeRange _2922_range = _2919___mcc_h695;
              DAST._IType _2923_b = _2918___mcc_h694;
              {
                RAST._IExpr _out770;
                DCOMP._IOwnership _out771;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out772;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out770, out _out771, out _out772);
                r = _out770;
                resultingOwnership = _out771;
                readIdents = _out772;
              }
            }
          } else if (_source128.is_Nullable) {
            DAST._IType _2924___mcc_h700 = _source128.dtor_Nullable_a0;
            {
              RAST._IExpr _out773;
              DCOMP._IOwnership _out774;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out775;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out773, out _out774, out _out775);
              r = _out773;
              resultingOwnership = _out774;
              readIdents = _out775;
            }
          } else if (_source128.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2925___mcc_h702 = _source128.dtor_Tuple_a0;
            {
              RAST._IExpr _out776;
              DCOMP._IOwnership _out777;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out778;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out776, out _out777, out _out778);
              r = _out776;
              resultingOwnership = _out777;
              readIdents = _out778;
            }
          } else if (_source128.is_Array) {
            DAST._IType _2926___mcc_h704 = _source128.dtor_element;
            BigInteger _2927___mcc_h705 = _source128.dtor_dims;
            {
              RAST._IExpr _out779;
              DCOMP._IOwnership _out780;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out779, out _out780, out _out781);
              r = _out779;
              resultingOwnership = _out780;
              readIdents = _out781;
            }
          } else if (_source128.is_Seq) {
            DAST._IType _2928___mcc_h708 = _source128.dtor_element;
            {
              RAST._IExpr _out782;
              DCOMP._IOwnership _out783;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out784;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out782, out _out783, out _out784);
              r = _out782;
              resultingOwnership = _out783;
              readIdents = _out784;
            }
          } else if (_source128.is_Set) {
            DAST._IType _2929___mcc_h710 = _source128.dtor_element;
            {
              RAST._IExpr _out785;
              DCOMP._IOwnership _out786;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out787;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out785, out _out786, out _out787);
              r = _out785;
              resultingOwnership = _out786;
              readIdents = _out787;
            }
          } else if (_source128.is_Multiset) {
            DAST._IType _2930___mcc_h712 = _source128.dtor_element;
            {
              RAST._IExpr _out788;
              DCOMP._IOwnership _out789;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out790;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out788, out _out789, out _out790);
              r = _out788;
              resultingOwnership = _out789;
              readIdents = _out790;
            }
          } else if (_source128.is_Map) {
            DAST._IType _2931___mcc_h714 = _source128.dtor_key;
            DAST._IType _2932___mcc_h715 = _source128.dtor_value;
            {
              RAST._IExpr _out791;
              DCOMP._IOwnership _out792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out791, out _out792, out _out793);
              r = _out791;
              resultingOwnership = _out792;
              readIdents = _out793;
            }
          } else if (_source128.is_SetBuilder) {
            DAST._IType _2933___mcc_h718 = _source128.dtor_element;
            {
              RAST._IExpr _out794;
              DCOMP._IOwnership _out795;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out796;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out794, out _out795, out _out796);
              r = _out794;
              resultingOwnership = _out795;
              readIdents = _out796;
            }
          } else if (_source128.is_MapBuilder) {
            DAST._IType _2934___mcc_h720 = _source128.dtor_key;
            DAST._IType _2935___mcc_h721 = _source128.dtor_value;
            {
              RAST._IExpr _out797;
              DCOMP._IOwnership _out798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out799;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out797, out _out798, out _out799);
              r = _out797;
              resultingOwnership = _out798;
              readIdents = _out799;
            }
          } else if (_source128.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2936___mcc_h724 = _source128.dtor_args;
            DAST._IType _2937___mcc_h725 = _source128.dtor_result;
            {
              RAST._IExpr _out800;
              DCOMP._IOwnership _out801;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out802;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out800, out _out801, out _out802);
              r = _out800;
              resultingOwnership = _out801;
              readIdents = _out802;
            }
          } else if (_source128.is_Primitive) {
            DAST._IPrimitive _2938___mcc_h728 = _source128.dtor_Primitive_a0;
            {
              RAST._IExpr _out803;
              DCOMP._IOwnership _out804;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out803, out _out804, out _out805);
              r = _out803;
              resultingOwnership = _out804;
              readIdents = _out805;
            }
          } else if (_source128.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2939___mcc_h730 = _source128.dtor_Passthrough_a0;
            {
              RAST._IExpr _out806;
              DCOMP._IOwnership _out807;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out808;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out806, out _out807, out _out808);
              r = _out806;
              resultingOwnership = _out807;
              readIdents = _out808;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2940___mcc_h732 = _source128.dtor_TypeArg_a0;
            {
              RAST._IExpr _out809;
              DCOMP._IOwnership _out810;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out811;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out809, out _out810, out _out811);
              r = _out809;
              resultingOwnership = _out810;
              readIdents = _out811;
            }
          }
        } else if (_source104.is_Arrow) {
          Dafny.ISequence<DAST._IType> _2941___mcc_h734 = _source104.dtor_args;
          DAST._IType _2942___mcc_h735 = _source104.dtor_result;
          DAST._IType _source130 = _2545___mcc_h1;
          if (_source130.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2943___mcc_h742 = _source130.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2944___mcc_h743 = _source130.dtor_typeArgs;
            DAST._IResolvedType _2945___mcc_h744 = _source130.dtor_resolved;
            DAST._IResolvedType _source131 = _2945___mcc_h744;
            if (_source131.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2946___mcc_h748 = _source131.dtor_path;
              {
                RAST._IExpr _out812;
                DCOMP._IOwnership _out813;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out814;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out812, out _out813, out _out814);
                r = _out812;
                resultingOwnership = _out813;
                readIdents = _out814;
              }
            } else if (_source131.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2947___mcc_h750 = _source131.dtor_path;
              {
                RAST._IExpr _out815;
                DCOMP._IOwnership _out816;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out817;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out815, out _out816, out _out817);
                r = _out815;
                resultingOwnership = _out816;
                readIdents = _out817;
              }
            } else {
              DAST._IType _2948___mcc_h752 = _source131.dtor_baseType;
              DAST._INewtypeRange _2949___mcc_h753 = _source131.dtor_range;
              bool _2950___mcc_h754 = _source131.dtor_erase;
              bool _2951_erase = _2950___mcc_h754;
              DAST._INewtypeRange _2952_range = _2949___mcc_h753;
              DAST._IType _2953_b = _2948___mcc_h752;
              {
                RAST._IExpr _out818;
                DCOMP._IOwnership _out819;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out820;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out818, out _out819, out _out820);
                r = _out818;
                resultingOwnership = _out819;
                readIdents = _out820;
              }
            }
          } else if (_source130.is_Nullable) {
            DAST._IType _2954___mcc_h758 = _source130.dtor_Nullable_a0;
            {
              RAST._IExpr _out821;
              DCOMP._IOwnership _out822;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out823;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out821, out _out822, out _out823);
              r = _out821;
              resultingOwnership = _out822;
              readIdents = _out823;
            }
          } else if (_source130.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2955___mcc_h760 = _source130.dtor_Tuple_a0;
            {
              RAST._IExpr _out824;
              DCOMP._IOwnership _out825;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out824, out _out825, out _out826);
              r = _out824;
              resultingOwnership = _out825;
              readIdents = _out826;
            }
          } else if (_source130.is_Array) {
            DAST._IType _2956___mcc_h762 = _source130.dtor_element;
            BigInteger _2957___mcc_h763 = _source130.dtor_dims;
            {
              RAST._IExpr _out827;
              DCOMP._IOwnership _out828;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out829;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out827, out _out828, out _out829);
              r = _out827;
              resultingOwnership = _out828;
              readIdents = _out829;
            }
          } else if (_source130.is_Seq) {
            DAST._IType _2958___mcc_h766 = _source130.dtor_element;
            {
              RAST._IExpr _out830;
              DCOMP._IOwnership _out831;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out832;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out830, out _out831, out _out832);
              r = _out830;
              resultingOwnership = _out831;
              readIdents = _out832;
            }
          } else if (_source130.is_Set) {
            DAST._IType _2959___mcc_h768 = _source130.dtor_element;
            {
              RAST._IExpr _out833;
              DCOMP._IOwnership _out834;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out835;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out833, out _out834, out _out835);
              r = _out833;
              resultingOwnership = _out834;
              readIdents = _out835;
            }
          } else if (_source130.is_Multiset) {
            DAST._IType _2960___mcc_h770 = _source130.dtor_element;
            {
              RAST._IExpr _out836;
              DCOMP._IOwnership _out837;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out836, out _out837, out _out838);
              r = _out836;
              resultingOwnership = _out837;
              readIdents = _out838;
            }
          } else if (_source130.is_Map) {
            DAST._IType _2961___mcc_h772 = _source130.dtor_key;
            DAST._IType _2962___mcc_h773 = _source130.dtor_value;
            {
              RAST._IExpr _out839;
              DCOMP._IOwnership _out840;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out841;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out839, out _out840, out _out841);
              r = _out839;
              resultingOwnership = _out840;
              readIdents = _out841;
            }
          } else if (_source130.is_SetBuilder) {
            DAST._IType _2963___mcc_h776 = _source130.dtor_element;
            {
              RAST._IExpr _out842;
              DCOMP._IOwnership _out843;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out844;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out842, out _out843, out _out844);
              r = _out842;
              resultingOwnership = _out843;
              readIdents = _out844;
            }
          } else if (_source130.is_MapBuilder) {
            DAST._IType _2964___mcc_h778 = _source130.dtor_key;
            DAST._IType _2965___mcc_h779 = _source130.dtor_value;
            {
              RAST._IExpr _out845;
              DCOMP._IOwnership _out846;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out847;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out845, out _out846, out _out847);
              r = _out845;
              resultingOwnership = _out846;
              readIdents = _out847;
            }
          } else if (_source130.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2966___mcc_h782 = _source130.dtor_args;
            DAST._IType _2967___mcc_h783 = _source130.dtor_result;
            {
              RAST._IExpr _out848;
              DCOMP._IOwnership _out849;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out848, out _out849, out _out850);
              r = _out848;
              resultingOwnership = _out849;
              readIdents = _out850;
            }
          } else if (_source130.is_Primitive) {
            DAST._IPrimitive _2968___mcc_h786 = _source130.dtor_Primitive_a0;
            {
              RAST._IExpr _out851;
              DCOMP._IOwnership _out852;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out853;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out851, out _out852, out _out853);
              r = _out851;
              resultingOwnership = _out852;
              readIdents = _out853;
            }
          } else if (_source130.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2969___mcc_h788 = _source130.dtor_Passthrough_a0;
            {
              RAST._IExpr _out854;
              DCOMP._IOwnership _out855;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out856;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out854, out _out855, out _out856);
              r = _out854;
              resultingOwnership = _out855;
              readIdents = _out856;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2970___mcc_h790 = _source130.dtor_TypeArg_a0;
            {
              RAST._IExpr _out857;
              DCOMP._IOwnership _out858;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out859;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out857, out _out858, out _out859);
              r = _out857;
              resultingOwnership = _out858;
              readIdents = _out859;
            }
          }
        } else if (_source104.is_Primitive) {
          DAST._IPrimitive _2971___mcc_h792 = _source104.dtor_Primitive_a0;
          DAST._IPrimitive _source132 = _2971___mcc_h792;
          if (_source132.is_Int) {
            DAST._IType _source133 = _2545___mcc_h1;
            if (_source133.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2972___mcc_h796 = _source133.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2973___mcc_h797 = _source133.dtor_typeArgs;
              DAST._IResolvedType _2974___mcc_h798 = _source133.dtor_resolved;
              DAST._IResolvedType _source134 = _2974___mcc_h798;
              if (_source134.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2975___mcc_h802 = _source134.dtor_path;
                {
                  RAST._IExpr _out860;
                  DCOMP._IOwnership _out861;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out860, out _out861, out _out862);
                  r = _out860;
                  resultingOwnership = _out861;
                  readIdents = _out862;
                }
              } else if (_source134.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2976___mcc_h804 = _source134.dtor_path;
                {
                  RAST._IExpr _out863;
                  DCOMP._IOwnership _out864;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out865;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out863, out _out864, out _out865);
                  r = _out863;
                  resultingOwnership = _out864;
                  readIdents = _out865;
                }
              } else {
                DAST._IType _2977___mcc_h806 = _source134.dtor_baseType;
                DAST._INewtypeRange _2978___mcc_h807 = _source134.dtor_range;
                bool _2979___mcc_h808 = _source134.dtor_erase;
                bool _2980_erase = _2979___mcc_h808;
                DAST._INewtypeRange _2981_range = _2978___mcc_h807;
                DAST._IType _2982_b = _2977___mcc_h806;
                {
                  RAST._IExpr _out866;
                  DCOMP._IOwnership _out867;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out868;
                  (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out866, out _out867, out _out868);
                  r = _out866;
                  resultingOwnership = _out867;
                  readIdents = _out868;
                }
              }
            } else if (_source133.is_Nullable) {
              DAST._IType _2983___mcc_h812 = _source133.dtor_Nullable_a0;
              {
                RAST._IExpr _out869;
                DCOMP._IOwnership _out870;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out871;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out869, out _out870, out _out871);
                r = _out869;
                resultingOwnership = _out870;
                readIdents = _out871;
              }
            } else if (_source133.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2984___mcc_h814 = _source133.dtor_Tuple_a0;
              {
                RAST._IExpr _out872;
                DCOMP._IOwnership _out873;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out872, out _out873, out _out874);
                r = _out872;
                resultingOwnership = _out873;
                readIdents = _out874;
              }
            } else if (_source133.is_Array) {
              DAST._IType _2985___mcc_h816 = _source133.dtor_element;
              BigInteger _2986___mcc_h817 = _source133.dtor_dims;
              {
                RAST._IExpr _out875;
                DCOMP._IOwnership _out876;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out877;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out875, out _out876, out _out877);
                r = _out875;
                resultingOwnership = _out876;
                readIdents = _out877;
              }
            } else if (_source133.is_Seq) {
              DAST._IType _2987___mcc_h820 = _source133.dtor_element;
              {
                RAST._IExpr _out878;
                DCOMP._IOwnership _out879;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out880;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out878, out _out879, out _out880);
                r = _out878;
                resultingOwnership = _out879;
                readIdents = _out880;
              }
            } else if (_source133.is_Set) {
              DAST._IType _2988___mcc_h822 = _source133.dtor_element;
              {
                RAST._IExpr _out881;
                DCOMP._IOwnership _out882;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out881, out _out882, out _out883);
                r = _out881;
                resultingOwnership = _out882;
                readIdents = _out883;
              }
            } else if (_source133.is_Multiset) {
              DAST._IType _2989___mcc_h824 = _source133.dtor_element;
              {
                RAST._IExpr _out884;
                DCOMP._IOwnership _out885;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out886;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out884, out _out885, out _out886);
                r = _out884;
                resultingOwnership = _out885;
                readIdents = _out886;
              }
            } else if (_source133.is_Map) {
              DAST._IType _2990___mcc_h826 = _source133.dtor_key;
              DAST._IType _2991___mcc_h827 = _source133.dtor_value;
              {
                RAST._IExpr _out887;
                DCOMP._IOwnership _out888;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out889;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out887, out _out888, out _out889);
                r = _out887;
                resultingOwnership = _out888;
                readIdents = _out889;
              }
            } else if (_source133.is_SetBuilder) {
              DAST._IType _2992___mcc_h830 = _source133.dtor_element;
              {
                RAST._IExpr _out890;
                DCOMP._IOwnership _out891;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out892;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out890, out _out891, out _out892);
                r = _out890;
                resultingOwnership = _out891;
                readIdents = _out892;
              }
            } else if (_source133.is_MapBuilder) {
              DAST._IType _2993___mcc_h832 = _source133.dtor_key;
              DAST._IType _2994___mcc_h833 = _source133.dtor_value;
              {
                RAST._IExpr _out893;
                DCOMP._IOwnership _out894;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out893, out _out894, out _out895);
                r = _out893;
                resultingOwnership = _out894;
                readIdents = _out895;
              }
            } else if (_source133.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2995___mcc_h836 = _source133.dtor_args;
              DAST._IType _2996___mcc_h837 = _source133.dtor_result;
              {
                RAST._IExpr _out896;
                DCOMP._IOwnership _out897;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out898;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out896, out _out897, out _out898);
                r = _out896;
                resultingOwnership = _out897;
                readIdents = _out898;
              }
            } else if (_source133.is_Primitive) {
              DAST._IPrimitive _2997___mcc_h840 = _source133.dtor_Primitive_a0;
              DAST._IPrimitive _source135 = _2997___mcc_h840;
              if (_source135.is_Int) {
                {
                  RAST._IExpr _out899;
                  DCOMP._IOwnership _out900;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out901;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out899, out _out900, out _out901);
                  r = _out899;
                  resultingOwnership = _out900;
                  readIdents = _out901;
                }
              } else if (_source135.is_Real) {
                {
                  RAST._IExpr _2998_recursiveGen;
                  DCOMP._IOwnership _2999___v74;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3000_recIdents;
                  RAST._IExpr _out902;
                  DCOMP._IOwnership _out903;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out904;
                  (this).GenExpr(_2538_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out902, out _out903, out _out904);
                  _2998_recursiveGen = _out902;
                  _2999___v74 = _out903;
                  _3000_recIdents = _out904;
                  r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_2998_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                  RAST._IExpr _out905;
                  DCOMP._IOwnership _out906;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out905, out _out906);
                  r = _out905;
                  resultingOwnership = _out906;
                  readIdents = _3000_recIdents;
                }
              } else if (_source135.is_String) {
                {
                  RAST._IExpr _out907;
                  DCOMP._IOwnership _out908;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out909;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out907, out _out908, out _out909);
                  r = _out907;
                  resultingOwnership = _out908;
                  readIdents = _out909;
                }
              } else if (_source135.is_Bool) {
                {
                  RAST._IExpr _out910;
                  DCOMP._IOwnership _out911;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out912;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out910, out _out911, out _out912);
                  r = _out910;
                  resultingOwnership = _out911;
                  readIdents = _out912;
                }
              } else {
                {
                  RAST._IType _3001_rhsType;
                  RAST._IType _out913;
                  _out913 = (this).GenType(_2540_toTpe, true, false);
                  _3001_rhsType = _out913;
                  RAST._IExpr _3002_recursiveGen;
                  DCOMP._IOwnership _3003___v80;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3004_recIdents;
                  RAST._IExpr _out914;
                  DCOMP._IOwnership _out915;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out916;
                  (this).GenExpr(_2538_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out914, out _out915, out _out916);
                  _3002_recursiveGen = _out914;
                  _3003___v80 = _out915;
                  _3004_recIdents = _out916;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_3002_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                  RAST._IExpr _out917;
                  DCOMP._IOwnership _out918;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out917, out _out918);
                  r = _out917;
                  resultingOwnership = _out918;
                  readIdents = _3004_recIdents;
                }
              }
            } else if (_source133.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3005___mcc_h842 = _source133.dtor_Passthrough_a0;
              {
                RAST._IType _3006_rhsType;
                RAST._IType _out919;
                _out919 = (this).GenType(_2540_toTpe, true, false);
                _3006_rhsType = _out919;
                RAST._IExpr _3007_recursiveGen;
                DCOMP._IOwnership _3008___v77;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3009_recIdents;
                RAST._IExpr _out920;
                DCOMP._IOwnership _out921;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out922;
                (this).GenExpr(_2538_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out920, out _out921, out _out922);
                _3007_recursiveGen = _out920;
                _3008___v77 = _out921;
                _3009_recIdents = _out922;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3006_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_3007_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                RAST._IExpr _out923;
                DCOMP._IOwnership _out924;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out923, out _out924);
                r = _out923;
                resultingOwnership = _out924;
                readIdents = _3009_recIdents;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3010___mcc_h844 = _source133.dtor_TypeArg_a0;
              {
                RAST._IExpr _out925;
                DCOMP._IOwnership _out926;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out927;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out925, out _out926, out _out927);
                r = _out925;
                resultingOwnership = _out926;
                readIdents = _out927;
              }
            }
          } else if (_source132.is_Real) {
            DAST._IType _source136 = _2545___mcc_h1;
            if (_source136.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3011___mcc_h846 = _source136.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _3012___mcc_h847 = _source136.dtor_typeArgs;
              DAST._IResolvedType _3013___mcc_h848 = _source136.dtor_resolved;
              DAST._IResolvedType _source137 = _3013___mcc_h848;
              if (_source137.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3014___mcc_h852 = _source137.dtor_path;
                {
                  RAST._IExpr _out928;
                  DCOMP._IOwnership _out929;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out930;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out928, out _out929, out _out930);
                  r = _out928;
                  resultingOwnership = _out929;
                  readIdents = _out930;
                }
              } else if (_source137.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3015___mcc_h854 = _source137.dtor_path;
                {
                  RAST._IExpr _out931;
                  DCOMP._IOwnership _out932;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out933;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out931, out _out932, out _out933);
                  r = _out931;
                  resultingOwnership = _out932;
                  readIdents = _out933;
                }
              } else {
                DAST._IType _3016___mcc_h856 = _source137.dtor_baseType;
                DAST._INewtypeRange _3017___mcc_h857 = _source137.dtor_range;
                bool _3018___mcc_h858 = _source137.dtor_erase;
                bool _3019_erase = _3018___mcc_h858;
                DAST._INewtypeRange _3020_range = _3017___mcc_h857;
                DAST._IType _3021_b = _3016___mcc_h856;
                {
                  RAST._IExpr _out934;
                  DCOMP._IOwnership _out935;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out936;
                  (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out934, out _out935, out _out936);
                  r = _out934;
                  resultingOwnership = _out935;
                  readIdents = _out936;
                }
              }
            } else if (_source136.is_Nullable) {
              DAST._IType _3022___mcc_h862 = _source136.dtor_Nullable_a0;
              {
                RAST._IExpr _out937;
                DCOMP._IOwnership _out938;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out939;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out937, out _out938, out _out939);
                r = _out937;
                resultingOwnership = _out938;
                readIdents = _out939;
              }
            } else if (_source136.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3023___mcc_h864 = _source136.dtor_Tuple_a0;
              {
                RAST._IExpr _out940;
                DCOMP._IOwnership _out941;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out942;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out940, out _out941, out _out942);
                r = _out940;
                resultingOwnership = _out941;
                readIdents = _out942;
              }
            } else if (_source136.is_Array) {
              DAST._IType _3024___mcc_h866 = _source136.dtor_element;
              BigInteger _3025___mcc_h867 = _source136.dtor_dims;
              {
                RAST._IExpr _out943;
                DCOMP._IOwnership _out944;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out945;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out943, out _out944, out _out945);
                r = _out943;
                resultingOwnership = _out944;
                readIdents = _out945;
              }
            } else if (_source136.is_Seq) {
              DAST._IType _3026___mcc_h870 = _source136.dtor_element;
              {
                RAST._IExpr _out946;
                DCOMP._IOwnership _out947;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out948;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out946, out _out947, out _out948);
                r = _out946;
                resultingOwnership = _out947;
                readIdents = _out948;
              }
            } else if (_source136.is_Set) {
              DAST._IType _3027___mcc_h872 = _source136.dtor_element;
              {
                RAST._IExpr _out949;
                DCOMP._IOwnership _out950;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out951;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out949, out _out950, out _out951);
                r = _out949;
                resultingOwnership = _out950;
                readIdents = _out951;
              }
            } else if (_source136.is_Multiset) {
              DAST._IType _3028___mcc_h874 = _source136.dtor_element;
              {
                RAST._IExpr _out952;
                DCOMP._IOwnership _out953;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out954;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out952, out _out953, out _out954);
                r = _out952;
                resultingOwnership = _out953;
                readIdents = _out954;
              }
            } else if (_source136.is_Map) {
              DAST._IType _3029___mcc_h876 = _source136.dtor_key;
              DAST._IType _3030___mcc_h877 = _source136.dtor_value;
              {
                RAST._IExpr _out955;
                DCOMP._IOwnership _out956;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out957;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out955, out _out956, out _out957);
                r = _out955;
                resultingOwnership = _out956;
                readIdents = _out957;
              }
            } else if (_source136.is_SetBuilder) {
              DAST._IType _3031___mcc_h880 = _source136.dtor_element;
              {
                RAST._IExpr _out958;
                DCOMP._IOwnership _out959;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out960;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out958, out _out959, out _out960);
                r = _out958;
                resultingOwnership = _out959;
                readIdents = _out960;
              }
            } else if (_source136.is_MapBuilder) {
              DAST._IType _3032___mcc_h882 = _source136.dtor_key;
              DAST._IType _3033___mcc_h883 = _source136.dtor_value;
              {
                RAST._IExpr _out961;
                DCOMP._IOwnership _out962;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out963;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out961, out _out962, out _out963);
                r = _out961;
                resultingOwnership = _out962;
                readIdents = _out963;
              }
            } else if (_source136.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3034___mcc_h886 = _source136.dtor_args;
              DAST._IType _3035___mcc_h887 = _source136.dtor_result;
              {
                RAST._IExpr _out964;
                DCOMP._IOwnership _out965;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out964, out _out965, out _out966);
                r = _out964;
                resultingOwnership = _out965;
                readIdents = _out966;
              }
            } else if (_source136.is_Primitive) {
              DAST._IPrimitive _3036___mcc_h890 = _source136.dtor_Primitive_a0;
              DAST._IPrimitive _source138 = _3036___mcc_h890;
              if (_source138.is_Int) {
                {
                  RAST._IExpr _3037_recursiveGen;
                  DCOMP._IOwnership _3038___v75;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3039_recIdents;
                  RAST._IExpr _out967;
                  DCOMP._IOwnership _out968;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out969;
                  (this).GenExpr(_2538_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out967, out _out968, out _out969);
                  _3037_recursiveGen = _out967;
                  _3038___v75 = _out968;
                  _3039_recIdents = _out969;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_3037_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                  RAST._IExpr _out970;
                  DCOMP._IOwnership _out971;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out970, out _out971);
                  r = _out970;
                  resultingOwnership = _out971;
                  readIdents = _3039_recIdents;
                }
              } else if (_source138.is_Real) {
                {
                  RAST._IExpr _out972;
                  DCOMP._IOwnership _out973;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out972, out _out973, out _out974);
                  r = _out972;
                  resultingOwnership = _out973;
                  readIdents = _out974;
                }
              } else if (_source138.is_String) {
                {
                  RAST._IExpr _out975;
                  DCOMP._IOwnership _out976;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out977;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out975, out _out976, out _out977);
                  r = _out975;
                  resultingOwnership = _out976;
                  readIdents = _out977;
                }
              } else if (_source138.is_Bool) {
                {
                  RAST._IExpr _out978;
                  DCOMP._IOwnership _out979;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out980;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out978, out _out979, out _out980);
                  r = _out978;
                  resultingOwnership = _out979;
                  readIdents = _out980;
                }
              } else {
                {
                  RAST._IExpr _out981;
                  DCOMP._IOwnership _out982;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out983;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out981, out _out982, out _out983);
                  r = _out981;
                  resultingOwnership = _out982;
                  readIdents = _out983;
                }
              }
            } else if (_source136.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3040___mcc_h892 = _source136.dtor_Passthrough_a0;
              {
                RAST._IExpr _out984;
                DCOMP._IOwnership _out985;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out986;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out984, out _out985, out _out986);
                r = _out984;
                resultingOwnership = _out985;
                readIdents = _out986;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3041___mcc_h894 = _source136.dtor_TypeArg_a0;
              {
                RAST._IExpr _out987;
                DCOMP._IOwnership _out988;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out989;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out987, out _out988, out _out989);
                r = _out987;
                resultingOwnership = _out988;
                readIdents = _out989;
              }
            }
          } else if (_source132.is_String) {
            DAST._IType _source139 = _2545___mcc_h1;
            if (_source139.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3042___mcc_h896 = _source139.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _3043___mcc_h897 = _source139.dtor_typeArgs;
              DAST._IResolvedType _3044___mcc_h898 = _source139.dtor_resolved;
              DAST._IResolvedType _source140 = _3044___mcc_h898;
              if (_source140.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3045___mcc_h902 = _source140.dtor_path;
                {
                  RAST._IExpr _out990;
                  DCOMP._IOwnership _out991;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out992;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out990, out _out991, out _out992);
                  r = _out990;
                  resultingOwnership = _out991;
                  readIdents = _out992;
                }
              } else if (_source140.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3046___mcc_h904 = _source140.dtor_path;
                {
                  RAST._IExpr _out993;
                  DCOMP._IOwnership _out994;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out995;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out993, out _out994, out _out995);
                  r = _out993;
                  resultingOwnership = _out994;
                  readIdents = _out995;
                }
              } else {
                DAST._IType _3047___mcc_h906 = _source140.dtor_baseType;
                DAST._INewtypeRange _3048___mcc_h907 = _source140.dtor_range;
                bool _3049___mcc_h908 = _source140.dtor_erase;
                bool _3050_erase = _3049___mcc_h908;
                DAST._INewtypeRange _3051_range = _3048___mcc_h907;
                DAST._IType _3052_b = _3047___mcc_h906;
                {
                  RAST._IExpr _out996;
                  DCOMP._IOwnership _out997;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out998;
                  (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out996, out _out997, out _out998);
                  r = _out996;
                  resultingOwnership = _out997;
                  readIdents = _out998;
                }
              }
            } else if (_source139.is_Nullable) {
              DAST._IType _3053___mcc_h912 = _source139.dtor_Nullable_a0;
              {
                RAST._IExpr _out999;
                DCOMP._IOwnership _out1000;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1001;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out999, out _out1000, out _out1001);
                r = _out999;
                resultingOwnership = _out1000;
                readIdents = _out1001;
              }
            } else if (_source139.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3054___mcc_h914 = _source139.dtor_Tuple_a0;
              {
                RAST._IExpr _out1002;
                DCOMP._IOwnership _out1003;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1004;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1002, out _out1003, out _out1004);
                r = _out1002;
                resultingOwnership = _out1003;
                readIdents = _out1004;
              }
            } else if (_source139.is_Array) {
              DAST._IType _3055___mcc_h916 = _source139.dtor_element;
              BigInteger _3056___mcc_h917 = _source139.dtor_dims;
              {
                RAST._IExpr _out1005;
                DCOMP._IOwnership _out1006;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1007;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1005, out _out1006, out _out1007);
                r = _out1005;
                resultingOwnership = _out1006;
                readIdents = _out1007;
              }
            } else if (_source139.is_Seq) {
              DAST._IType _3057___mcc_h920 = _source139.dtor_element;
              {
                RAST._IExpr _out1008;
                DCOMP._IOwnership _out1009;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1010;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1008, out _out1009, out _out1010);
                r = _out1008;
                resultingOwnership = _out1009;
                readIdents = _out1010;
              }
            } else if (_source139.is_Set) {
              DAST._IType _3058___mcc_h922 = _source139.dtor_element;
              {
                RAST._IExpr _out1011;
                DCOMP._IOwnership _out1012;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1013;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1011, out _out1012, out _out1013);
                r = _out1011;
                resultingOwnership = _out1012;
                readIdents = _out1013;
              }
            } else if (_source139.is_Multiset) {
              DAST._IType _3059___mcc_h924 = _source139.dtor_element;
              {
                RAST._IExpr _out1014;
                DCOMP._IOwnership _out1015;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1016;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1014, out _out1015, out _out1016);
                r = _out1014;
                resultingOwnership = _out1015;
                readIdents = _out1016;
              }
            } else if (_source139.is_Map) {
              DAST._IType _3060___mcc_h926 = _source139.dtor_key;
              DAST._IType _3061___mcc_h927 = _source139.dtor_value;
              {
                RAST._IExpr _out1017;
                DCOMP._IOwnership _out1018;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1019;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1017, out _out1018, out _out1019);
                r = _out1017;
                resultingOwnership = _out1018;
                readIdents = _out1019;
              }
            } else if (_source139.is_SetBuilder) {
              DAST._IType _3062___mcc_h930 = _source139.dtor_element;
              {
                RAST._IExpr _out1020;
                DCOMP._IOwnership _out1021;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1022;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1020, out _out1021, out _out1022);
                r = _out1020;
                resultingOwnership = _out1021;
                readIdents = _out1022;
              }
            } else if (_source139.is_MapBuilder) {
              DAST._IType _3063___mcc_h932 = _source139.dtor_key;
              DAST._IType _3064___mcc_h933 = _source139.dtor_value;
              {
                RAST._IExpr _out1023;
                DCOMP._IOwnership _out1024;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1025;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1023, out _out1024, out _out1025);
                r = _out1023;
                resultingOwnership = _out1024;
                readIdents = _out1025;
              }
            } else if (_source139.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3065___mcc_h936 = _source139.dtor_args;
              DAST._IType _3066___mcc_h937 = _source139.dtor_result;
              {
                RAST._IExpr _out1026;
                DCOMP._IOwnership _out1027;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1028;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1026, out _out1027, out _out1028);
                r = _out1026;
                resultingOwnership = _out1027;
                readIdents = _out1028;
              }
            } else if (_source139.is_Primitive) {
              DAST._IPrimitive _3067___mcc_h940 = _source139.dtor_Primitive_a0;
              {
                RAST._IExpr _out1029;
                DCOMP._IOwnership _out1030;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1031;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1029, out _out1030, out _out1031);
                r = _out1029;
                resultingOwnership = _out1030;
                readIdents = _out1031;
              }
            } else if (_source139.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3068___mcc_h942 = _source139.dtor_Passthrough_a0;
              {
                RAST._IExpr _out1032;
                DCOMP._IOwnership _out1033;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1034;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1032, out _out1033, out _out1034);
                r = _out1032;
                resultingOwnership = _out1033;
                readIdents = _out1034;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3069___mcc_h944 = _source139.dtor_TypeArg_a0;
              {
                RAST._IExpr _out1035;
                DCOMP._IOwnership _out1036;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1037;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1035, out _out1036, out _out1037);
                r = _out1035;
                resultingOwnership = _out1036;
                readIdents = _out1037;
              }
            }
          } else if (_source132.is_Bool) {
            DAST._IType _source141 = _2545___mcc_h1;
            if (_source141.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3070___mcc_h946 = _source141.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _3071___mcc_h947 = _source141.dtor_typeArgs;
              DAST._IResolvedType _3072___mcc_h948 = _source141.dtor_resolved;
              DAST._IResolvedType _source142 = _3072___mcc_h948;
              if (_source142.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3073___mcc_h952 = _source142.dtor_path;
                {
                  RAST._IExpr _out1038;
                  DCOMP._IOwnership _out1039;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1040;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1038, out _out1039, out _out1040);
                  r = _out1038;
                  resultingOwnership = _out1039;
                  readIdents = _out1040;
                }
              } else if (_source142.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3074___mcc_h954 = _source142.dtor_path;
                {
                  RAST._IExpr _out1041;
                  DCOMP._IOwnership _out1042;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1043;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1041, out _out1042, out _out1043);
                  r = _out1041;
                  resultingOwnership = _out1042;
                  readIdents = _out1043;
                }
              } else {
                DAST._IType _3075___mcc_h956 = _source142.dtor_baseType;
                DAST._INewtypeRange _3076___mcc_h957 = _source142.dtor_range;
                bool _3077___mcc_h958 = _source142.dtor_erase;
                bool _3078_erase = _3077___mcc_h958;
                DAST._INewtypeRange _3079_range = _3076___mcc_h957;
                DAST._IType _3080_b = _3075___mcc_h956;
                {
                  RAST._IExpr _out1044;
                  DCOMP._IOwnership _out1045;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1046;
                  (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out1044, out _out1045, out _out1046);
                  r = _out1044;
                  resultingOwnership = _out1045;
                  readIdents = _out1046;
                }
              }
            } else if (_source141.is_Nullable) {
              DAST._IType _3081___mcc_h962 = _source141.dtor_Nullable_a0;
              {
                RAST._IExpr _out1047;
                DCOMP._IOwnership _out1048;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1049;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1047, out _out1048, out _out1049);
                r = _out1047;
                resultingOwnership = _out1048;
                readIdents = _out1049;
              }
            } else if (_source141.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3082___mcc_h964 = _source141.dtor_Tuple_a0;
              {
                RAST._IExpr _out1050;
                DCOMP._IOwnership _out1051;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1052;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1050, out _out1051, out _out1052);
                r = _out1050;
                resultingOwnership = _out1051;
                readIdents = _out1052;
              }
            } else if (_source141.is_Array) {
              DAST._IType _3083___mcc_h966 = _source141.dtor_element;
              BigInteger _3084___mcc_h967 = _source141.dtor_dims;
              {
                RAST._IExpr _out1053;
                DCOMP._IOwnership _out1054;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1053, out _out1054, out _out1055);
                r = _out1053;
                resultingOwnership = _out1054;
                readIdents = _out1055;
              }
            } else if (_source141.is_Seq) {
              DAST._IType _3085___mcc_h970 = _source141.dtor_element;
              {
                RAST._IExpr _out1056;
                DCOMP._IOwnership _out1057;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1058;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1056, out _out1057, out _out1058);
                r = _out1056;
                resultingOwnership = _out1057;
                readIdents = _out1058;
              }
            } else if (_source141.is_Set) {
              DAST._IType _3086___mcc_h972 = _source141.dtor_element;
              {
                RAST._IExpr _out1059;
                DCOMP._IOwnership _out1060;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1061;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1059, out _out1060, out _out1061);
                r = _out1059;
                resultingOwnership = _out1060;
                readIdents = _out1061;
              }
            } else if (_source141.is_Multiset) {
              DAST._IType _3087___mcc_h974 = _source141.dtor_element;
              {
                RAST._IExpr _out1062;
                DCOMP._IOwnership _out1063;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1064;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1062, out _out1063, out _out1064);
                r = _out1062;
                resultingOwnership = _out1063;
                readIdents = _out1064;
              }
            } else if (_source141.is_Map) {
              DAST._IType _3088___mcc_h976 = _source141.dtor_key;
              DAST._IType _3089___mcc_h977 = _source141.dtor_value;
              {
                RAST._IExpr _out1065;
                DCOMP._IOwnership _out1066;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1065, out _out1066, out _out1067);
                r = _out1065;
                resultingOwnership = _out1066;
                readIdents = _out1067;
              }
            } else if (_source141.is_SetBuilder) {
              DAST._IType _3090___mcc_h980 = _source141.dtor_element;
              {
                RAST._IExpr _out1068;
                DCOMP._IOwnership _out1069;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1070;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1068, out _out1069, out _out1070);
                r = _out1068;
                resultingOwnership = _out1069;
                readIdents = _out1070;
              }
            } else if (_source141.is_MapBuilder) {
              DAST._IType _3091___mcc_h982 = _source141.dtor_key;
              DAST._IType _3092___mcc_h983 = _source141.dtor_value;
              {
                RAST._IExpr _out1071;
                DCOMP._IOwnership _out1072;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1073;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1071, out _out1072, out _out1073);
                r = _out1071;
                resultingOwnership = _out1072;
                readIdents = _out1073;
              }
            } else if (_source141.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3093___mcc_h986 = _source141.dtor_args;
              DAST._IType _3094___mcc_h987 = _source141.dtor_result;
              {
                RAST._IExpr _out1074;
                DCOMP._IOwnership _out1075;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1076;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1074, out _out1075, out _out1076);
                r = _out1074;
                resultingOwnership = _out1075;
                readIdents = _out1076;
              }
            } else if (_source141.is_Primitive) {
              DAST._IPrimitive _3095___mcc_h990 = _source141.dtor_Primitive_a0;
              {
                RAST._IExpr _out1077;
                DCOMP._IOwnership _out1078;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1077, out _out1078, out _out1079);
                r = _out1077;
                resultingOwnership = _out1078;
                readIdents = _out1079;
              }
            } else if (_source141.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3096___mcc_h992 = _source141.dtor_Passthrough_a0;
              {
                RAST._IExpr _out1080;
                DCOMP._IOwnership _out1081;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1082;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1080, out _out1081, out _out1082);
                r = _out1080;
                resultingOwnership = _out1081;
                readIdents = _out1082;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3097___mcc_h994 = _source141.dtor_TypeArg_a0;
              {
                RAST._IExpr _out1083;
                DCOMP._IOwnership _out1084;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1085;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1083, out _out1084, out _out1085);
                r = _out1083;
                resultingOwnership = _out1084;
                readIdents = _out1085;
              }
            }
          } else {
            DAST._IType _source143 = _2545___mcc_h1;
            if (_source143.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3098___mcc_h996 = _source143.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _3099___mcc_h997 = _source143.dtor_typeArgs;
              DAST._IResolvedType _3100___mcc_h998 = _source143.dtor_resolved;
              DAST._IResolvedType _source144 = _3100___mcc_h998;
              if (_source144.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3101___mcc_h1002 = _source144.dtor_path;
                {
                  RAST._IExpr _out1086;
                  DCOMP._IOwnership _out1087;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1088;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1086, out _out1087, out _out1088);
                  r = _out1086;
                  resultingOwnership = _out1087;
                  readIdents = _out1088;
                }
              } else if (_source144.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3102___mcc_h1004 = _source144.dtor_path;
                {
                  RAST._IExpr _out1089;
                  DCOMP._IOwnership _out1090;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1089, out _out1090, out _out1091);
                  r = _out1089;
                  resultingOwnership = _out1090;
                  readIdents = _out1091;
                }
              } else {
                DAST._IType _3103___mcc_h1006 = _source144.dtor_baseType;
                DAST._INewtypeRange _3104___mcc_h1007 = _source144.dtor_range;
                bool _3105___mcc_h1008 = _source144.dtor_erase;
                bool _3106_erase = _3105___mcc_h1008;
                DAST._INewtypeRange _3107_range = _3104___mcc_h1007;
                DAST._IType _3108_b = _3103___mcc_h1006;
                {
                  RAST._IExpr _out1092;
                  DCOMP._IOwnership _out1093;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1094;
                  (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out1092, out _out1093, out _out1094);
                  r = _out1092;
                  resultingOwnership = _out1093;
                  readIdents = _out1094;
                }
              }
            } else if (_source143.is_Nullable) {
              DAST._IType _3109___mcc_h1012 = _source143.dtor_Nullable_a0;
              {
                RAST._IExpr _out1095;
                DCOMP._IOwnership _out1096;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1097;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1095, out _out1096, out _out1097);
                r = _out1095;
                resultingOwnership = _out1096;
                readIdents = _out1097;
              }
            } else if (_source143.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3110___mcc_h1014 = _source143.dtor_Tuple_a0;
              {
                RAST._IExpr _out1098;
                DCOMP._IOwnership _out1099;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1098, out _out1099, out _out1100);
                r = _out1098;
                resultingOwnership = _out1099;
                readIdents = _out1100;
              }
            } else if (_source143.is_Array) {
              DAST._IType _3111___mcc_h1016 = _source143.dtor_element;
              BigInteger _3112___mcc_h1017 = _source143.dtor_dims;
              {
                RAST._IExpr _out1101;
                DCOMP._IOwnership _out1102;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1103;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1101, out _out1102, out _out1103);
                r = _out1101;
                resultingOwnership = _out1102;
                readIdents = _out1103;
              }
            } else if (_source143.is_Seq) {
              DAST._IType _3113___mcc_h1020 = _source143.dtor_element;
              {
                RAST._IExpr _out1104;
                DCOMP._IOwnership _out1105;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1106;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1104, out _out1105, out _out1106);
                r = _out1104;
                resultingOwnership = _out1105;
                readIdents = _out1106;
              }
            } else if (_source143.is_Set) {
              DAST._IType _3114___mcc_h1022 = _source143.dtor_element;
              {
                RAST._IExpr _out1107;
                DCOMP._IOwnership _out1108;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1109;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1107, out _out1108, out _out1109);
                r = _out1107;
                resultingOwnership = _out1108;
                readIdents = _out1109;
              }
            } else if (_source143.is_Multiset) {
              DAST._IType _3115___mcc_h1024 = _source143.dtor_element;
              {
                RAST._IExpr _out1110;
                DCOMP._IOwnership _out1111;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1110, out _out1111, out _out1112);
                r = _out1110;
                resultingOwnership = _out1111;
                readIdents = _out1112;
              }
            } else if (_source143.is_Map) {
              DAST._IType _3116___mcc_h1026 = _source143.dtor_key;
              DAST._IType _3117___mcc_h1027 = _source143.dtor_value;
              {
                RAST._IExpr _out1113;
                DCOMP._IOwnership _out1114;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1115;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1113, out _out1114, out _out1115);
                r = _out1113;
                resultingOwnership = _out1114;
                readIdents = _out1115;
              }
            } else if (_source143.is_SetBuilder) {
              DAST._IType _3118___mcc_h1030 = _source143.dtor_element;
              {
                RAST._IExpr _out1116;
                DCOMP._IOwnership _out1117;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1118;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1116, out _out1117, out _out1118);
                r = _out1116;
                resultingOwnership = _out1117;
                readIdents = _out1118;
              }
            } else if (_source143.is_MapBuilder) {
              DAST._IType _3119___mcc_h1032 = _source143.dtor_key;
              DAST._IType _3120___mcc_h1033 = _source143.dtor_value;
              {
                RAST._IExpr _out1119;
                DCOMP._IOwnership _out1120;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1121;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1119, out _out1120, out _out1121);
                r = _out1119;
                resultingOwnership = _out1120;
                readIdents = _out1121;
              }
            } else if (_source143.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3121___mcc_h1036 = _source143.dtor_args;
              DAST._IType _3122___mcc_h1037 = _source143.dtor_result;
              {
                RAST._IExpr _out1122;
                DCOMP._IOwnership _out1123;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1122, out _out1123, out _out1124);
                r = _out1122;
                resultingOwnership = _out1123;
                readIdents = _out1124;
              }
            } else if (_source143.is_Primitive) {
              DAST._IPrimitive _3123___mcc_h1040 = _source143.dtor_Primitive_a0;
              DAST._IPrimitive _source145 = _3123___mcc_h1040;
              if (_source145.is_Int) {
                {
                  RAST._IType _3124_rhsType;
                  RAST._IType _out1125;
                  _out1125 = (this).GenType(_2539_fromTpe, true, false);
                  _3124_rhsType = _out1125;
                  RAST._IExpr _3125_recursiveGen;
                  DCOMP._IOwnership _3126___v81;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3127_recIdents;
                  RAST._IExpr _out1126;
                  DCOMP._IOwnership _out1127;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1128;
                  (this).GenExpr(_2538_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1126, out _out1127, out _out1128);
                  _3125_recursiveGen = _out1126;
                  _3126___v81 = _out1127;
                  _3127_recIdents = _out1128;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::BigInt::from("), (_3125_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)}")));
                  RAST._IExpr _out1129;
                  DCOMP._IOwnership _out1130;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1129, out _out1130);
                  r = _out1129;
                  resultingOwnership = _out1130;
                  readIdents = _3127_recIdents;
                }
              } else if (_source145.is_Real) {
                {
                  RAST._IExpr _out1131;
                  DCOMP._IOwnership _out1132;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1133;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1131, out _out1132, out _out1133);
                  r = _out1131;
                  resultingOwnership = _out1132;
                  readIdents = _out1133;
                }
              } else if (_source145.is_String) {
                {
                  RAST._IExpr _out1134;
                  DCOMP._IOwnership _out1135;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1134, out _out1135, out _out1136);
                  r = _out1134;
                  resultingOwnership = _out1135;
                  readIdents = _out1136;
                }
              } else if (_source145.is_Bool) {
                {
                  RAST._IExpr _out1137;
                  DCOMP._IOwnership _out1138;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1139;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1137, out _out1138, out _out1139);
                  r = _out1137;
                  resultingOwnership = _out1138;
                  readIdents = _out1139;
                }
              } else {
                {
                  RAST._IExpr _out1140;
                  DCOMP._IOwnership _out1141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1142;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1140, out _out1141, out _out1142);
                  r = _out1140;
                  resultingOwnership = _out1141;
                  readIdents = _out1142;
                }
              }
            } else if (_source143.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3128___mcc_h1042 = _source143.dtor_Passthrough_a0;
              {
                RAST._IExpr _out1143;
                DCOMP._IOwnership _out1144;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1145;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1143, out _out1144, out _out1145);
                r = _out1143;
                resultingOwnership = _out1144;
                readIdents = _out1145;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3129___mcc_h1044 = _source143.dtor_TypeArg_a0;
              {
                RAST._IExpr _out1146;
                DCOMP._IOwnership _out1147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1148;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1146, out _out1147, out _out1148);
                r = _out1146;
                resultingOwnership = _out1147;
                readIdents = _out1148;
              }
            }
          }
        } else if (_source104.is_Passthrough) {
          Dafny.ISequence<Dafny.Rune> _3130___mcc_h1046 = _source104.dtor_Passthrough_a0;
          DAST._IType _source146 = _2545___mcc_h1;
          if (_source146.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3131___mcc_h1050 = _source146.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _3132___mcc_h1051 = _source146.dtor_typeArgs;
            DAST._IResolvedType _3133___mcc_h1052 = _source146.dtor_resolved;
            DAST._IResolvedType _source147 = _3133___mcc_h1052;
            if (_source147.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3134___mcc_h1056 = _source147.dtor_path;
              {
                RAST._IExpr _out1149;
                DCOMP._IOwnership _out1150;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1151;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1149, out _out1150, out _out1151);
                r = _out1149;
                resultingOwnership = _out1150;
                readIdents = _out1151;
              }
            } else if (_source147.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3135___mcc_h1058 = _source147.dtor_path;
              {
                RAST._IExpr _out1152;
                DCOMP._IOwnership _out1153;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1154;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1152, out _out1153, out _out1154);
                r = _out1152;
                resultingOwnership = _out1153;
                readIdents = _out1154;
              }
            } else {
              DAST._IType _3136___mcc_h1060 = _source147.dtor_baseType;
              DAST._INewtypeRange _3137___mcc_h1061 = _source147.dtor_range;
              bool _3138___mcc_h1062 = _source147.dtor_erase;
              bool _3139_erase = _3138___mcc_h1062;
              DAST._INewtypeRange _3140_range = _3137___mcc_h1061;
              DAST._IType _3141_b = _3136___mcc_h1060;
              {
                RAST._IExpr _out1155;
                DCOMP._IOwnership _out1156;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1157;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out1155, out _out1156, out _out1157);
                r = _out1155;
                resultingOwnership = _out1156;
                readIdents = _out1157;
              }
            }
          } else if (_source146.is_Nullable) {
            DAST._IType _3142___mcc_h1066 = _source146.dtor_Nullable_a0;
            {
              RAST._IExpr _out1158;
              DCOMP._IOwnership _out1159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1160;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1158, out _out1159, out _out1160);
              r = _out1158;
              resultingOwnership = _out1159;
              readIdents = _out1160;
            }
          } else if (_source146.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3143___mcc_h1068 = _source146.dtor_Tuple_a0;
            {
              RAST._IExpr _out1161;
              DCOMP._IOwnership _out1162;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1163;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1161, out _out1162, out _out1163);
              r = _out1161;
              resultingOwnership = _out1162;
              readIdents = _out1163;
            }
          } else if (_source146.is_Array) {
            DAST._IType _3144___mcc_h1070 = _source146.dtor_element;
            BigInteger _3145___mcc_h1071 = _source146.dtor_dims;
            {
              RAST._IExpr _out1164;
              DCOMP._IOwnership _out1165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1166;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1164, out _out1165, out _out1166);
              r = _out1164;
              resultingOwnership = _out1165;
              readIdents = _out1166;
            }
          } else if (_source146.is_Seq) {
            DAST._IType _3146___mcc_h1074 = _source146.dtor_element;
            {
              RAST._IExpr _out1167;
              DCOMP._IOwnership _out1168;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1167, out _out1168, out _out1169);
              r = _out1167;
              resultingOwnership = _out1168;
              readIdents = _out1169;
            }
          } else if (_source146.is_Set) {
            DAST._IType _3147___mcc_h1076 = _source146.dtor_element;
            {
              RAST._IExpr _out1170;
              DCOMP._IOwnership _out1171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1172;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1170, out _out1171, out _out1172);
              r = _out1170;
              resultingOwnership = _out1171;
              readIdents = _out1172;
            }
          } else if (_source146.is_Multiset) {
            DAST._IType _3148___mcc_h1078 = _source146.dtor_element;
            {
              RAST._IExpr _out1173;
              DCOMP._IOwnership _out1174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1175;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1173, out _out1174, out _out1175);
              r = _out1173;
              resultingOwnership = _out1174;
              readIdents = _out1175;
            }
          } else if (_source146.is_Map) {
            DAST._IType _3149___mcc_h1080 = _source146.dtor_key;
            DAST._IType _3150___mcc_h1081 = _source146.dtor_value;
            {
              RAST._IExpr _out1176;
              DCOMP._IOwnership _out1177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1178;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1176, out _out1177, out _out1178);
              r = _out1176;
              resultingOwnership = _out1177;
              readIdents = _out1178;
            }
          } else if (_source146.is_SetBuilder) {
            DAST._IType _3151___mcc_h1084 = _source146.dtor_element;
            {
              RAST._IExpr _out1179;
              DCOMP._IOwnership _out1180;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1179, out _out1180, out _out1181);
              r = _out1179;
              resultingOwnership = _out1180;
              readIdents = _out1181;
            }
          } else if (_source146.is_MapBuilder) {
            DAST._IType _3152___mcc_h1086 = _source146.dtor_key;
            DAST._IType _3153___mcc_h1087 = _source146.dtor_value;
            {
              RAST._IExpr _out1182;
              DCOMP._IOwnership _out1183;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1184;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1182, out _out1183, out _out1184);
              r = _out1182;
              resultingOwnership = _out1183;
              readIdents = _out1184;
            }
          } else if (_source146.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3154___mcc_h1090 = _source146.dtor_args;
            DAST._IType _3155___mcc_h1091 = _source146.dtor_result;
            {
              RAST._IExpr _out1185;
              DCOMP._IOwnership _out1186;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1187;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1185, out _out1186, out _out1187);
              r = _out1185;
              resultingOwnership = _out1186;
              readIdents = _out1187;
            }
          } else if (_source146.is_Primitive) {
            DAST._IPrimitive _3156___mcc_h1094 = _source146.dtor_Primitive_a0;
            DAST._IPrimitive _source148 = _3156___mcc_h1094;
            if (_source148.is_Int) {
              {
                RAST._IType _3157_rhsType;
                RAST._IType _out1188;
                _out1188 = (this).GenType(_2539_fromTpe, true, false);
                _3157_rhsType = _out1188;
                RAST._IExpr _3158_recursiveGen;
                DCOMP._IOwnership _3159___v79;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3160_recIdents;
                RAST._IExpr _out1189;
                DCOMP._IOwnership _out1190;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1191;
                (this).GenExpr(_2538_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1189, out _out1190, out _out1191);
                _3158_recursiveGen = _out1189;
                _3159___v79 = _out1190;
                _3160_recIdents = _out1191;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_3158_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                RAST._IExpr _out1192;
                DCOMP._IOwnership _out1193;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1192, out _out1193);
                r = _out1192;
                resultingOwnership = _out1193;
                readIdents = _3160_recIdents;
              }
            } else if (_source148.is_Real) {
              {
                RAST._IExpr _out1194;
                DCOMP._IOwnership _out1195;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1196;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1194, out _out1195, out _out1196);
                r = _out1194;
                resultingOwnership = _out1195;
                readIdents = _out1196;
              }
            } else if (_source148.is_String) {
              {
                RAST._IExpr _out1197;
                DCOMP._IOwnership _out1198;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1199;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1197, out _out1198, out _out1199);
                r = _out1197;
                resultingOwnership = _out1198;
                readIdents = _out1199;
              }
            } else if (_source148.is_Bool) {
              {
                RAST._IExpr _out1200;
                DCOMP._IOwnership _out1201;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1202;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1200, out _out1201, out _out1202);
                r = _out1200;
                resultingOwnership = _out1201;
                readIdents = _out1202;
              }
            } else {
              {
                RAST._IExpr _out1203;
                DCOMP._IOwnership _out1204;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1205;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1203, out _out1204, out _out1205);
                r = _out1203;
                resultingOwnership = _out1204;
                readIdents = _out1205;
              }
            }
          } else if (_source146.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3161___mcc_h1096 = _source146.dtor_Passthrough_a0;
            {
              RAST._IExpr _3162_recursiveGen;
              DCOMP._IOwnership _3163___v84;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3164_recIdents;
              RAST._IExpr _out1206;
              DCOMP._IOwnership _out1207;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1208;
              (this).GenExpr(_2538_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1206, out _out1207, out _out1208);
              _3162_recursiveGen = _out1206;
              _3163___v84 = _out1207;
              _3164_recIdents = _out1208;
              RAST._IType _3165_toTpeGen;
              RAST._IType _out1209;
              _out1209 = (this).GenType(_2540_toTpe, true, false);
              _3165_toTpeGen = _out1209;
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_3162_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_3165_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
              RAST._IExpr _out1210;
              DCOMP._IOwnership _out1211;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1210, out _out1211);
              r = _out1210;
              resultingOwnership = _out1211;
              readIdents = _3164_recIdents;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3166___mcc_h1098 = _source146.dtor_TypeArg_a0;
            {
              RAST._IExpr _out1212;
              DCOMP._IOwnership _out1213;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1214;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1212, out _out1213, out _out1214);
              r = _out1212;
              resultingOwnership = _out1213;
              readIdents = _out1214;
            }
          }
        } else {
          Dafny.ISequence<Dafny.Rune> _3167___mcc_h1100 = _source104.dtor_TypeArg_a0;
          DAST._IType _source149 = _2545___mcc_h1;
          if (_source149.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3168___mcc_h1104 = _source149.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _3169___mcc_h1105 = _source149.dtor_typeArgs;
            DAST._IResolvedType _3170___mcc_h1106 = _source149.dtor_resolved;
            DAST._IResolvedType _source150 = _3170___mcc_h1106;
            if (_source150.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3171___mcc_h1110 = _source150.dtor_path;
              {
                RAST._IExpr _out1215;
                DCOMP._IOwnership _out1216;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1217;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1215, out _out1216, out _out1217);
                r = _out1215;
                resultingOwnership = _out1216;
                readIdents = _out1217;
              }
            } else if (_source150.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3172___mcc_h1112 = _source150.dtor_path;
              {
                RAST._IExpr _out1218;
                DCOMP._IOwnership _out1219;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1220;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1218, out _out1219, out _out1220);
                r = _out1218;
                resultingOwnership = _out1219;
                readIdents = _out1220;
              }
            } else {
              DAST._IType _3173___mcc_h1114 = _source150.dtor_baseType;
              DAST._INewtypeRange _3174___mcc_h1115 = _source150.dtor_range;
              bool _3175___mcc_h1116 = _source150.dtor_erase;
              bool _3176_erase = _3175___mcc_h1116;
              DAST._INewtypeRange _3177_range = _3174___mcc_h1115;
              DAST._IType _3178_b = _3173___mcc_h1114;
              {
                RAST._IExpr _out1221;
                DCOMP._IOwnership _out1222;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1223;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out1221, out _out1222, out _out1223);
                r = _out1221;
                resultingOwnership = _out1222;
                readIdents = _out1223;
              }
            }
          } else if (_source149.is_Nullable) {
            DAST._IType _3179___mcc_h1120 = _source149.dtor_Nullable_a0;
            {
              RAST._IExpr _out1224;
              DCOMP._IOwnership _out1225;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1224, out _out1225, out _out1226);
              r = _out1224;
              resultingOwnership = _out1225;
              readIdents = _out1226;
            }
          } else if (_source149.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3180___mcc_h1122 = _source149.dtor_Tuple_a0;
            {
              RAST._IExpr _out1227;
              DCOMP._IOwnership _out1228;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1229;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1227, out _out1228, out _out1229);
              r = _out1227;
              resultingOwnership = _out1228;
              readIdents = _out1229;
            }
          } else if (_source149.is_Array) {
            DAST._IType _3181___mcc_h1124 = _source149.dtor_element;
            BigInteger _3182___mcc_h1125 = _source149.dtor_dims;
            {
              RAST._IExpr _out1230;
              DCOMP._IOwnership _out1231;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1232;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1230, out _out1231, out _out1232);
              r = _out1230;
              resultingOwnership = _out1231;
              readIdents = _out1232;
            }
          } else if (_source149.is_Seq) {
            DAST._IType _3183___mcc_h1128 = _source149.dtor_element;
            {
              RAST._IExpr _out1233;
              DCOMP._IOwnership _out1234;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1235;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1233, out _out1234, out _out1235);
              r = _out1233;
              resultingOwnership = _out1234;
              readIdents = _out1235;
            }
          } else if (_source149.is_Set) {
            DAST._IType _3184___mcc_h1130 = _source149.dtor_element;
            {
              RAST._IExpr _out1236;
              DCOMP._IOwnership _out1237;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1238;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1236, out _out1237, out _out1238);
              r = _out1236;
              resultingOwnership = _out1237;
              readIdents = _out1238;
            }
          } else if (_source149.is_Multiset) {
            DAST._IType _3185___mcc_h1132 = _source149.dtor_element;
            {
              RAST._IExpr _out1239;
              DCOMP._IOwnership _out1240;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1241;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1239, out _out1240, out _out1241);
              r = _out1239;
              resultingOwnership = _out1240;
              readIdents = _out1241;
            }
          } else if (_source149.is_Map) {
            DAST._IType _3186___mcc_h1134 = _source149.dtor_key;
            DAST._IType _3187___mcc_h1135 = _source149.dtor_value;
            {
              RAST._IExpr _out1242;
              DCOMP._IOwnership _out1243;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1244;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1242, out _out1243, out _out1244);
              r = _out1242;
              resultingOwnership = _out1243;
              readIdents = _out1244;
            }
          } else if (_source149.is_SetBuilder) {
            DAST._IType _3188___mcc_h1138 = _source149.dtor_element;
            {
              RAST._IExpr _out1245;
              DCOMP._IOwnership _out1246;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1245, out _out1246, out _out1247);
              r = _out1245;
              resultingOwnership = _out1246;
              readIdents = _out1247;
            }
          } else if (_source149.is_MapBuilder) {
            DAST._IType _3189___mcc_h1140 = _source149.dtor_key;
            DAST._IType _3190___mcc_h1141 = _source149.dtor_value;
            {
              RAST._IExpr _out1248;
              DCOMP._IOwnership _out1249;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1250;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1248, out _out1249, out _out1250);
              r = _out1248;
              resultingOwnership = _out1249;
              readIdents = _out1250;
            }
          } else if (_source149.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3191___mcc_h1144 = _source149.dtor_args;
            DAST._IType _3192___mcc_h1145 = _source149.dtor_result;
            {
              RAST._IExpr _out1251;
              DCOMP._IOwnership _out1252;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1253;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1251, out _out1252, out _out1253);
              r = _out1251;
              resultingOwnership = _out1252;
              readIdents = _out1253;
            }
          } else if (_source149.is_Primitive) {
            DAST._IPrimitive _3193___mcc_h1148 = _source149.dtor_Primitive_a0;
            {
              RAST._IExpr _out1254;
              DCOMP._IOwnership _out1255;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1256;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1254, out _out1255, out _out1256);
              r = _out1254;
              resultingOwnership = _out1255;
              readIdents = _out1256;
            }
          } else if (_source149.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3194___mcc_h1150 = _source149.dtor_Passthrough_a0;
            {
              RAST._IExpr _out1257;
              DCOMP._IOwnership _out1258;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1257, out _out1258, out _out1259);
              r = _out1257;
              resultingOwnership = _out1258;
              readIdents = _out1259;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3195___mcc_h1152 = _source149.dtor_TypeArg_a0;
            {
              RAST._IExpr _out1260;
              DCOMP._IOwnership _out1261;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1262;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1260, out _out1261, out _out1262);
              r = _out1260;
              resultingOwnership = _out1261;
              readIdents = _out1262;
            }
          }
        }
      }
      return ;
    }
    public void GenExpr(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source151 = e;
      if (_source151.is_Literal) {
        DAST._ILiteral _3196___mcc_h0 = _source151.dtor_Literal_a0;
        RAST._IExpr _out1263;
        DCOMP._IOwnership _out1264;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1265;
        (this).GenExprLiteral(e, selfIdent, @params, expectedOwnership, out _out1263, out _out1264, out _out1265);
        r = _out1263;
        resultingOwnership = _out1264;
        readIdents = _out1265;
      } else if (_source151.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _3197___mcc_h1 = _source151.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _3198_name = _3197___mcc_h1;
        {
          r = RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent(_3198_name));
          bool _3199_currentlyBorrowed;
          _3199_currentlyBorrowed = (@params).Contains(_3198_name);
          if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
            r = RAST.__default.BorrowMut(r);
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
          } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
            r = RAST.__default.Clone(r);
            resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          } else if (_3199_currentlyBorrowed) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          } else {
            r = RAST.__default.Borrow(r);
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3198_name);
          return ;
        }
      } else if (_source151.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3200___mcc_h2 = _source151.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3201_path = _3200___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _3202_p;
          Dafny.ISequence<Dafny.Rune> _out1266;
          _out1266 = DCOMP.COMP.GenPath(_3201_path);
          _3202_p = _out1266;
          r = RAST.Expr.create_RawExpr(_3202_p);
          RAST._IExpr _out1267;
          DCOMP._IOwnership _out1268;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1267, out _out1268);
          r = _out1267;
          resultingOwnership = _out1268;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source151.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _3203___mcc_h3 = _source151.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _3204_values = _3203___mcc_h3;
        {
          Dafny.ISequence<Dafny.Rune> _3205_s;
          _3205_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3206_i;
          _3206_i = BigInteger.Zero;
          while ((_3206_i) < (new BigInteger((_3204_values).Count))) {
            if ((_3206_i).Sign == 1) {
              _3205_s = Dafny.Sequence<Dafny.Rune>.Concat(_3205_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            RAST._IExpr _3207_recursiveGen;
            DCOMP._IOwnership _3208___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3209_recIdents;
            RAST._IExpr _out1269;
            DCOMP._IOwnership _out1270;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1271;
            (this).GenExpr((_3204_values).Select(_3206_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1269, out _out1270, out _out1271);
            _3207_recursiveGen = _out1269;
            _3208___v87 = _out1270;
            _3209_recIdents = _out1271;
            _3205_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3205_s, (_3207_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3209_recIdents);
            _3206_i = (_3206_i) + (BigInteger.One);
          }
          _3205_s = Dafny.Sequence<Dafny.Rune>.Concat(_3205_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          r = RAST.Expr.create_RawExpr(_3205_s);
          RAST._IExpr _out1272;
          DCOMP._IOwnership _out1273;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1272, out _out1273);
          r = _out1272;
          resultingOwnership = _out1273;
          return ;
        }
      } else if (_source151.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3210___mcc_h4 = _source151.dtor_path;
        Dafny.ISequence<DAST._IType> _3211___mcc_h5 = _source151.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _3212___mcc_h6 = _source151.dtor_args;
        Dafny.ISequence<DAST._IExpression> _3213_args = _3212___mcc_h6;
        Dafny.ISequence<DAST._IType> _3214_typeArgs = _3211___mcc_h5;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3215_path = _3210___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _3216_path;
          Dafny.ISequence<Dafny.Rune> _out1274;
          _out1274 = DCOMP.COMP.GenPath(_3215_path);
          _3216_path = _out1274;
          Dafny.ISequence<Dafny.Rune> _3217_s;
          _3217_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _3216_path);
          if ((new BigInteger((_3214_typeArgs).Count)).Sign == 1) {
            BigInteger _3218_i;
            _3218_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IType> _3219_typeExprs;
            _3219_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            while ((_3218_i) < (new BigInteger((_3214_typeArgs).Count))) {
              RAST._IType _3220_typeExpr;
              RAST._IType _out1275;
              _out1275 = (this).GenType((_3214_typeArgs).Select(_3218_i), false, false);
              _3220_typeExpr = _out1275;
              _3219_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_3219_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_3220_typeExpr));
              _3218_i = (_3218_i) + (BigInteger.One);
            }
            _3217_s = Dafny.Sequence<Dafny.Rune>.Concat(_3217_s, (RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _3219_typeExprs))._ToString(DCOMP.__default.IND));
          }
          _3217_s = Dafny.Sequence<Dafny.Rune>.Concat(_3217_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3221_i;
          _3221_i = BigInteger.Zero;
          while ((_3221_i) < (new BigInteger((_3213_args).Count))) {
            if ((_3221_i).Sign == 1) {
              _3217_s = Dafny.Sequence<Dafny.Rune>.Concat(_3217_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IExpr _3222_recursiveGen;
            DCOMP._IOwnership _3223___v88;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3224_recIdents;
            RAST._IExpr _out1276;
            DCOMP._IOwnership _out1277;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1278;
            (this).GenExpr((_3213_args).Select(_3221_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1276, out _out1277, out _out1278);
            _3222_recursiveGen = _out1276;
            _3223___v88 = _out1277;
            _3224_recIdents = _out1278;
            _3217_s = Dafny.Sequence<Dafny.Rune>.Concat(_3217_s, (_3222_recursiveGen)._ToString(DCOMP.__default.IND));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3224_recIdents);
            _3221_i = (_3221_i) + (BigInteger.One);
          }
          _3217_s = Dafny.Sequence<Dafny.Rune>.Concat(_3217_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          r = RAST.Expr.create_RawExpr(_3217_s);
          RAST._IExpr _out1279;
          DCOMP._IOwnership _out1280;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1279, out _out1280);
          r = _out1279;
          resultingOwnership = _out1280;
          return ;
        }
      } else if (_source151.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _3225___mcc_h7 = _source151.dtor_dims;
        DAST._IType _3226___mcc_h8 = _source151.dtor_typ;
        DAST._IType _3227_typ = _3226___mcc_h8;
        Dafny.ISequence<DAST._IExpression> _3228_dims = _3225___mcc_h7;
        {
          BigInteger _3229_i;
          _3229_i = (new BigInteger((_3228_dims).Count)) - (BigInteger.One);
          RAST._IType _3230_genTyp;
          RAST._IType _out1281;
          _out1281 = (this).GenType(_3227_typ, false, false);
          _3230_genTyp = _out1281;
          Dafny.ISequence<Dafny.Rune> _3231_s;
          _3231_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3230_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_3229_i).Sign != -1) {
            RAST._IExpr _3232_recursiveGen;
            DCOMP._IOwnership _3233___v89;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3234_recIdents;
            RAST._IExpr _out1282;
            DCOMP._IOwnership _out1283;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1284;
            (this).GenExpr((_3228_dims).Select(_3229_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1282, out _out1283, out _out1284);
            _3232_recursiveGen = _out1282;
            _3233___v89 = _out1283;
            _3234_recIdents = _out1284;
            _3231_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _3231_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_3232_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3234_recIdents);
            _3229_i = (_3229_i) - (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(_3231_s);
          RAST._IExpr _out1285;
          DCOMP._IOwnership _out1286;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1285, out _out1286);
          r = _out1285;
          resultingOwnership = _out1286;
          return ;
        }
      } else if (_source151.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3235___mcc_h9 = _source151.dtor_path;
        Dafny.ISequence<DAST._IType> _3236___mcc_h10 = _source151.dtor_typeArgs;
        Dafny.ISequence<Dafny.Rune> _3237___mcc_h11 = _source151.dtor_variant;
        bool _3238___mcc_h12 = _source151.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3239___mcc_h13 = _source151.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3240_values = _3239___mcc_h13;
        bool _3241_isCo = _3238___mcc_h12;
        Dafny.ISequence<Dafny.Rune> _3242_variant = _3237___mcc_h11;
        Dafny.ISequence<DAST._IType> _3243_typeArgs = _3236___mcc_h10;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3244_path = _3235___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _3245_path;
          Dafny.ISequence<Dafny.Rune> _out1287;
          _out1287 = DCOMP.COMP.GenPath(_3244_path);
          _3245_path = _out1287;
          Dafny.ISequence<Dafny.Rune> _3246_s;
          _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _3245_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          if ((new BigInteger((_3243_typeArgs).Count)).Sign == 1) {
            _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
            BigInteger _3247_i;
            _3247_i = BigInteger.Zero;
            while ((_3247_i) < (new BigInteger((_3243_typeArgs).Count))) {
              if ((_3247_i).Sign == 1) {
                _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              RAST._IType _3248_typeExpr;
              RAST._IType _out1288;
              _out1288 = (this).GenType((_3243_typeArgs).Select(_3247_i), false, false);
              _3248_typeExpr = _out1288;
              _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, (_3248_typeExpr)._ToString(DCOMP.__default.IND));
              _3247_i = (_3247_i) + (BigInteger.One);
            }
            _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::"));
          }
          _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, DCOMP.__default.escapeIdent(_3242_variant));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3249_i;
          _3249_i = BigInteger.Zero;
          _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_3249_i) < (new BigInteger((_3240_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs60 = (_3240_values).Select(_3249_i);
            Dafny.ISequence<Dafny.Rune> _3250_name = _let_tmp_rhs60.dtor__0;
            DAST._IExpression _3251_value = _let_tmp_rhs60.dtor__1;
            if ((_3249_i).Sign == 1) {
              _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_3241_isCo) {
              RAST._IExpr _3252_recursiveGen;
              DCOMP._IOwnership _3253___v90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3254_recIdents;
              RAST._IExpr _out1289;
              DCOMP._IOwnership _out1290;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1291;
              (this).GenExpr(_3251_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out1289, out _out1290, out _out1291);
              _3252_recursiveGen = _out1289;
              _3253___v90 = _out1290;
              _3254_recIdents = _out1291;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3254_recIdents);
              Dafny.ISequence<Dafny.Rune> _3255_allReadCloned;
              _3255_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_3254_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _3256_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_3254_recIdents).Elements) {
                  _3256_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                  if ((_3254_recIdents).Contains(_3256_next)) {
                    goto after__ASSIGN_SUCH_THAT_2;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 2852)");
              after__ASSIGN_SUCH_THAT_2: ;
                _3255_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3255_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent(_3256_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), DCOMP.__default.escapeIdent(_3256_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _3254_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_3254_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3256_next));
              }
              _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, DCOMP.__default.escapeIdent(_3250_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _3255_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_3252_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              RAST._IExpr _3257_recursiveGen;
              DCOMP._IOwnership _3258___v91;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3259_recIdents;
              RAST._IExpr _out1292;
              DCOMP._IOwnership _out1293;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1294;
              (this).GenExpr(_3251_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1292, out _out1293, out _out1294);
              _3257_recursiveGen = _out1292;
              _3258___v91 = _out1293;
              _3259_recIdents = _out1294;
              _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, DCOMP.__default.escapeIdent(_3250_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_3257_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3259_recIdents);
            }
            _3249_i = (_3249_i) + (BigInteger.One);
          }
          _3246_s = Dafny.Sequence<Dafny.Rune>.Concat(_3246_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          r = RAST.Expr.create_RawExpr(_3246_s);
          RAST._IExpr _out1295;
          DCOMP._IOwnership _out1296;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1295, out _out1296);
          r = _out1295;
          resultingOwnership = _out1296;
          return ;
        }
      } else if (_source151.is_Convert) {
        DAST._IExpression _3260___mcc_h14 = _source151.dtor_value;
        DAST._IType _3261___mcc_h15 = _source151.dtor_from;
        DAST._IType _3262___mcc_h16 = _source151.dtor_typ;
        {
          RAST._IExpr _out1297;
          DCOMP._IOwnership _out1298;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1299;
          (this).GenExprConvert(e, selfIdent, @params, expectedOwnership, out _out1297, out _out1298, out _out1299);
          r = _out1297;
          resultingOwnership = _out1298;
          readIdents = _out1299;
        }
      } else if (_source151.is_SeqConstruct) {
        DAST._IExpression _3263___mcc_h17 = _source151.dtor_length;
        DAST._IExpression _3264___mcc_h18 = _source151.dtor_elem;
        DAST._IExpression _3265_expr = _3264___mcc_h18;
        DAST._IExpression _3266_length = _3263___mcc_h17;
        {
          RAST._IExpr _3267_recursiveGen;
          DCOMP._IOwnership _3268___v95;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3269_recIdents;
          RAST._IExpr _out1300;
          DCOMP._IOwnership _out1301;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1302;
          (this).GenExpr(_3265_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1300, out _out1301, out _out1302);
          _3267_recursiveGen = _out1300;
          _3268___v95 = _out1301;
          _3269_recIdents = _out1302;
          RAST._IExpr _3270_lengthGen;
          DCOMP._IOwnership _3271___v96;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3272_lengthIdents;
          RAST._IExpr _out1303;
          DCOMP._IOwnership _out1304;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
          (this).GenExpr(_3266_length, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1303, out _out1304, out _out1305);
          _3270_lengthGen = _out1303;
          _3271___v96 = _out1304;
          _3272_lengthIdents = _out1305;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_3267_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_3270_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer.0(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3269_recIdents, _3272_lengthIdents);
          RAST._IExpr _out1306;
          DCOMP._IOwnership _out1307;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1306, out _out1307);
          r = _out1306;
          resultingOwnership = _out1307;
          return ;
        }
      } else if (_source151.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _3273___mcc_h19 = _source151.dtor_elements;
        DAST._IType _3274___mcc_h20 = _source151.dtor_typ;
        DAST._IType _3275_typ = _3274___mcc_h20;
        Dafny.ISequence<DAST._IExpression> _3276_exprs = _3273___mcc_h19;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IType _3277_genTpe;
          RAST._IType _out1308;
          _out1308 = (this).GenType(_3275_typ, false, false);
          _3277_genTpe = _out1308;
          BigInteger _3278_i;
          _3278_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _3279_args;
          _3279_args = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_3278_i) < (new BigInteger((_3276_exprs).Count))) {
            RAST._IExpr _3280_recursiveGen;
            DCOMP._IOwnership _3281___v97;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3282_recIdents;
            RAST._IExpr _out1309;
            DCOMP._IOwnership _out1310;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1311;
            (this).GenExpr((_3276_exprs).Select(_3278_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1309, out _out1310, out _out1311);
            _3280_recursiveGen = _out1309;
            _3281___v97 = _out1310;
            _3282_recIdents = _out1311;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3282_recIdents);
            _3279_args = Dafny.Sequence<RAST._IExpr>.Concat(_3279_args, Dafny.Sequence<RAST._IExpr>.FromElements(_3280_recursiveGen));
            _3278_i = (_3278_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3279_args);
          if ((new BigInteger((_3279_args).Count)).Sign == 0) {
            r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_3277_genTpe));
          }
          RAST._IExpr _out1312;
          DCOMP._IOwnership _out1313;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1312, out _out1313);
          r = _out1312;
          resultingOwnership = _out1313;
          return ;
        }
      } else if (_source151.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _3283___mcc_h21 = _source151.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _3284_exprs = _3283___mcc_h21;
        {
          Dafny.ISequence<RAST._IExpr> _3285_generatedValues;
          _3285_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3286_i;
          _3286_i = BigInteger.Zero;
          while ((_3286_i) < (new BigInteger((_3284_exprs).Count))) {
            RAST._IExpr _3287_recursiveGen;
            DCOMP._IOwnership _3288___v98;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3289_recIdents;
            RAST._IExpr _out1314;
            DCOMP._IOwnership _out1315;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1316;
            (this).GenExpr((_3284_exprs).Select(_3286_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1314, out _out1315, out _out1316);
            _3287_recursiveGen = _out1314;
            _3288___v98 = _out1315;
            _3289_recIdents = _out1316;
            _3285_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_3285_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_3287_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3289_recIdents);
            _3286_i = (_3286_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3285_generatedValues);
          RAST._IExpr _out1317;
          DCOMP._IOwnership _out1318;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1317, out _out1318);
          r = _out1317;
          resultingOwnership = _out1318;
          return ;
        }
      } else if (_source151.is_MultisetValue) {
        Dafny.ISequence<DAST._IExpression> _3290___mcc_h22 = _source151.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _3291_exprs = _3290___mcc_h22;
        {
          Dafny.ISequence<RAST._IExpr> _3292_generatedValues;
          _3292_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3293_i;
          _3293_i = BigInteger.Zero;
          while ((_3293_i) < (new BigInteger((_3291_exprs).Count))) {
            RAST._IExpr _3294_recursiveGen;
            DCOMP._IOwnership _3295___v99;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3296_recIdents;
            RAST._IExpr _out1319;
            DCOMP._IOwnership _out1320;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1321;
            (this).GenExpr((_3291_exprs).Select(_3293_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1319, out _out1320, out _out1321);
            _3294_recursiveGen = _out1319;
            _3295___v99 = _out1320;
            _3296_recIdents = _out1321;
            _3292_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_3292_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_3294_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3296_recIdents);
            _3293_i = (_3293_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3292_generatedValues);
          RAST._IExpr _out1322;
          DCOMP._IOwnership _out1323;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1322, out _out1323);
          r = _out1322;
          resultingOwnership = _out1323;
          return ;
        }
      } else if (_source151.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3297___mcc_h23 = _source151.dtor_mapElems;
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3298_mapElems = _3297___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _3299_generatedValues;
          _3299_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3300_i;
          _3300_i = BigInteger.Zero;
          while ((_3300_i) < (new BigInteger((_3298_mapElems).Count))) {
            RAST._IExpr _3301_recursiveGenKey;
            DCOMP._IOwnership _3302___v101;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3303_recIdentsKey;
            RAST._IExpr _out1324;
            DCOMP._IOwnership _out1325;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1326;
            (this).GenExpr(((_3298_mapElems).Select(_3300_i)).dtor__0, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1324, out _out1325, out _out1326);
            _3301_recursiveGenKey = _out1324;
            _3302___v101 = _out1325;
            _3303_recIdentsKey = _out1326;
            RAST._IExpr _3304_recursiveGenValue;
            DCOMP._IOwnership _3305___v102;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3306_recIdentsValue;
            RAST._IExpr _out1327;
            DCOMP._IOwnership _out1328;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1329;
            (this).GenExpr(((_3298_mapElems).Select(_3300_i)).dtor__1, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1327, out _out1328, out _out1329);
            _3304_recursiveGenValue = _out1327;
            _3305___v102 = _out1328;
            _3306_recIdentsValue = _out1329;
            _3299_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_3299_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_3301_recursiveGenKey, _3304_recursiveGenValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3303_recIdentsKey), _3306_recIdentsValue);
            _3300_i = (_3300_i) + (BigInteger.One);
          }
          _3300_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _3307_arguments;
          _3307_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_3300_i) < (new BigInteger((_3299_generatedValues).Count))) {
            RAST._IExpr _3308_genKey;
            _3308_genKey = ((_3299_generatedValues).Select(_3300_i)).dtor__0;
            RAST._IExpr _3309_genValue;
            _3309_genValue = ((_3299_generatedValues).Select(_3300_i)).dtor__1;
            _3307_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3307_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _3308_genKey, _3309_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
            _3300_i = (_3300_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3307_arguments);
          RAST._IExpr _out1330;
          DCOMP._IOwnership _out1331;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1330, out _out1331);
          r = _out1330;
          resultingOwnership = _out1331;
          return ;
        }
      } else if (_source151.is_MapBuilder) {
        DAST._IType _3310___mcc_h24 = _source151.dtor_keyType;
        DAST._IType _3311___mcc_h25 = _source151.dtor_valueType;
        DAST._IType _3312_valueType = _3311___mcc_h25;
        DAST._IType _3313_keyType = _3310___mcc_h24;
        {
          RAST._IType _3314_kType;
          RAST._IType _out1332;
          _out1332 = (this).GenType(_3313_keyType, false, false);
          _3314_kType = _out1332;
          RAST._IType _3315_vType;
          RAST._IType _out1333;
          _out1333 = (this).GenType(_3312_valueType, false, false);
          _3315_vType = _out1333;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::MapBuilder::<"), (_3314_kType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), (_3315_vType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::new()")));
          RAST._IExpr _out1334;
          DCOMP._IOwnership _out1335;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1334, out _out1335);
          r = _out1334;
          resultingOwnership = _out1335;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source151.is_SeqUpdate) {
        DAST._IExpression _3316___mcc_h26 = _source151.dtor_expr;
        DAST._IExpression _3317___mcc_h27 = _source151.dtor_indexExpr;
        DAST._IExpression _3318___mcc_h28 = _source151.dtor_value;
        DAST._IExpression _3319_value = _3318___mcc_h28;
        DAST._IExpression _3320_index = _3317___mcc_h27;
        DAST._IExpression _3321_expr = _3316___mcc_h26;
        {
          RAST._IExpr _3322_exprR;
          DCOMP._IOwnership _3323___v103;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3324_exprIdents;
          RAST._IExpr _out1336;
          DCOMP._IOwnership _out1337;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1338;
          (this).GenExpr(_3321_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1336, out _out1337, out _out1338);
          _3322_exprR = _out1336;
          _3323___v103 = _out1337;
          _3324_exprIdents = _out1338;
          RAST._IExpr _3325_indexR;
          DCOMP._IOwnership _3326_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3327_indexIdents;
          RAST._IExpr _out1339;
          DCOMP._IOwnership _out1340;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1341;
          (this).GenExpr(_3320_index, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1339, out _out1340, out _out1341);
          _3325_indexR = _out1339;
          _3326_indexOwnership = _out1340;
          _3327_indexIdents = _out1341;
          RAST._IExpr _3328_valueR;
          DCOMP._IOwnership _3329_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3330_valueIdents;
          RAST._IExpr _out1342;
          DCOMP._IOwnership _out1343;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1344;
          (this).GenExpr(_3319_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1342, out _out1343, out _out1344);
          _3328_valueR = _out1342;
          _3329_valueOwnership = _out1343;
          _3330_valueIdents = _out1344;
          r = ((_3322_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_3325_indexR, _3328_valueR));
          RAST._IExpr _out1345;
          DCOMP._IOwnership _out1346;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1345, out _out1346);
          r = _out1345;
          resultingOwnership = _out1346;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3324_exprIdents, _3327_indexIdents), _3330_valueIdents);
          return ;
        }
      } else if (_source151.is_MapUpdate) {
        DAST._IExpression _3331___mcc_h29 = _source151.dtor_expr;
        DAST._IExpression _3332___mcc_h30 = _source151.dtor_indexExpr;
        DAST._IExpression _3333___mcc_h31 = _source151.dtor_value;
        DAST._IExpression _3334_value = _3333___mcc_h31;
        DAST._IExpression _3335_index = _3332___mcc_h30;
        DAST._IExpression _3336_expr = _3331___mcc_h29;
        {
          RAST._IExpr _3337_exprR;
          DCOMP._IOwnership _3338___v104;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3339_exprIdents;
          RAST._IExpr _out1347;
          DCOMP._IOwnership _out1348;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1349;
          (this).GenExpr(_3336_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1347, out _out1348, out _out1349);
          _3337_exprR = _out1347;
          _3338___v104 = _out1348;
          _3339_exprIdents = _out1349;
          RAST._IExpr _3340_indexR;
          DCOMP._IOwnership _3341_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3342_indexIdents;
          RAST._IExpr _out1350;
          DCOMP._IOwnership _out1351;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1352;
          (this).GenExpr(_3335_index, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1350, out _out1351, out _out1352);
          _3340_indexR = _out1350;
          _3341_indexOwnership = _out1351;
          _3342_indexIdents = _out1352;
          RAST._IExpr _3343_valueR;
          DCOMP._IOwnership _3344_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3345_valueIdents;
          RAST._IExpr _out1353;
          DCOMP._IOwnership _out1354;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1355;
          (this).GenExpr(_3334_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1353, out _out1354, out _out1355);
          _3343_valueR = _out1353;
          _3344_valueOwnership = _out1354;
          _3345_valueIdents = _out1355;
          r = ((_3337_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_3340_indexR, _3343_valueR));
          RAST._IExpr _out1356;
          DCOMP._IOwnership _out1357;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1356, out _out1357);
          r = _out1356;
          resultingOwnership = _out1357;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3339_exprIdents, _3342_indexIdents), _3345_valueIdents);
          return ;
        }
      } else if (_source151.is_SetBuilder) {
        DAST._IType _3346___mcc_h32 = _source151.dtor_elemType;
        DAST._IType _3347_elemType = _3346___mcc_h32;
        {
          RAST._IType _3348_eType;
          RAST._IType _out1358;
          _out1358 = (this).GenType(_3347_elemType, false, false);
          _3348_eType = _out1358;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::SetBuilder::<"), (_3348_eType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::new()")));
          RAST._IExpr _out1359;
          DCOMP._IOwnership _out1360;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1359, out _out1360);
          r = _out1359;
          resultingOwnership = _out1360;
          return ;
        }
      } else if (_source151.is_ToMultiset) {
        DAST._IExpression _3349___mcc_h33 = _source151.dtor_ToMultiset_a0;
        DAST._IExpression _3350_expr = _3349___mcc_h33;
        {
          RAST._IExpr _3351_recursiveGen;
          DCOMP._IOwnership _3352___v100;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3353_recIdents;
          RAST._IExpr _out1361;
          DCOMP._IOwnership _out1362;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1363;
          (this).GenExpr(_3350_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1361, out _out1362, out _out1363);
          _3351_recursiveGen = _out1361;
          _3352___v100 = _out1362;
          _3353_recIdents = _out1363;
          r = ((_3351_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          readIdents = _3353_recIdents;
          RAST._IExpr _out1364;
          DCOMP._IOwnership _out1365;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1364, out _out1365);
          r = _out1364;
          resultingOwnership = _out1365;
          return ;
        }
      } else if (_source151.is_This) {
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source152 = selfIdent;
          if (_source152.is_None) {
            {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
              RAST._IExpr _out1366;
              DCOMP._IOwnership _out1367;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1366, out _out1367);
              r = _out1366;
              resultingOwnership = _out1367;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3354___mcc_h273 = _source152.dtor_value;
            Dafny.ISequence<Dafny.Rune> _3355_id = _3354___mcc_h273;
            {
              r = RAST.Expr.create_RawExpr(_3355_id);
              if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                r = RAST.__default.Clone(r);
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                if (!(_3355_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.Borrow(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              } else {
                if (!(_3355_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.BorrowMut(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3355_id);
            }
          }
          return ;
        }
      } else if (_source151.is_Ite) {
        DAST._IExpression _3356___mcc_h34 = _source151.dtor_cond;
        DAST._IExpression _3357___mcc_h35 = _source151.dtor_thn;
        DAST._IExpression _3358___mcc_h36 = _source151.dtor_els;
        DAST._IExpression _3359_f = _3358___mcc_h36;
        DAST._IExpression _3360_t = _3357___mcc_h35;
        DAST._IExpression _3361_cond = _3356___mcc_h34;
        {
          RAST._IExpr _3362_cond;
          DCOMP._IOwnership _3363___v105;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3364_recIdentsCond;
          RAST._IExpr _out1368;
          DCOMP._IOwnership _out1369;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1370;
          (this).GenExpr(_3361_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1368, out _out1369, out _out1370);
          _3362_cond = _out1368;
          _3363___v105 = _out1369;
          _3364_recIdentsCond = _out1370;
          Dafny.ISequence<Dafny.Rune> _3365_condString;
          _3365_condString = (_3362_cond)._ToString(DCOMP.__default.IND);
          RAST._IExpr _3366___v106;
          DCOMP._IOwnership _3367_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3368___v107;
          RAST._IExpr _out1371;
          DCOMP._IOwnership _out1372;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1373;
          (this).GenExpr(_3360_t, selfIdent, @params, expectedOwnership, out _out1371, out _out1372, out _out1373);
          _3366___v106 = _out1371;
          _3367_tHasToBeOwned = _out1372;
          _3368___v107 = _out1373;
          RAST._IExpr _3369_fExpr;
          DCOMP._IOwnership _3370_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3371_recIdentsF;
          RAST._IExpr _out1374;
          DCOMP._IOwnership _out1375;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1376;
          (this).GenExpr(_3359_f, selfIdent, @params, _3367_tHasToBeOwned, out _out1374, out _out1375, out _out1376);
          _3369_fExpr = _out1374;
          _3370_fOwned = _out1375;
          _3371_recIdentsF = _out1376;
          Dafny.ISequence<Dafny.Rune> _3372_fString;
          _3372_fString = (_3369_fExpr)._ToString(DCOMP.__default.IND);
          RAST._IExpr _3373_tExpr;
          DCOMP._IOwnership _3374___v108;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3375_recIdentsT;
          RAST._IExpr _out1377;
          DCOMP._IOwnership _out1378;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1379;
          (this).GenExpr(_3360_t, selfIdent, @params, _3370_fOwned, out _out1377, out _out1378, out _out1379);
          _3373_tExpr = _out1377;
          _3374___v108 = _out1378;
          _3375_recIdentsT = _out1379;
          Dafny.ISequence<Dafny.Rune> _3376_tString;
          _3376_tString = (_3373_tExpr)._ToString(DCOMP.__default.IND);
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _3365_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _3376_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _3372_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
          RAST._IExpr _out1380;
          DCOMP._IOwnership _out1381;
          DCOMP.COMP.FromOwnership(r, _3370_fOwned, expectedOwnership, out _out1380, out _out1381);
          r = _out1380;
          resultingOwnership = _out1381;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3364_recIdentsCond, _3375_recIdentsT), _3371_recIdentsF);
          return ;
        }
      } else if (_source151.is_UnOp) {
        DAST._IUnaryOp _3377___mcc_h37 = _source151.dtor_unOp;
        DAST._IExpression _3378___mcc_h38 = _source151.dtor_expr;
        DAST.Format._IUnaryOpFormat _3379___mcc_h39 = _source151.dtor_format1;
        DAST._IUnaryOp _source153 = _3377___mcc_h37;
        if (_source153.is_Not) {
          DAST.Format._IUnaryOpFormat _3380_format = _3379___mcc_h39;
          DAST._IExpression _3381_e = _3378___mcc_h38;
          {
            RAST._IExpr _3382_recursiveGen;
            DCOMP._IOwnership _3383___v109;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3384_recIdents;
            RAST._IExpr _out1382;
            DCOMP._IOwnership _out1383;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1384;
            (this).GenExpr(_3381_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1382, out _out1383, out _out1384);
            _3382_recursiveGen = _out1382;
            _3383___v109 = _out1383;
            _3384_recIdents = _out1384;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _3382_recursiveGen, _3380_format);
            RAST._IExpr _out1385;
            DCOMP._IOwnership _out1386;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1385, out _out1386);
            r = _out1385;
            resultingOwnership = _out1386;
            readIdents = _3384_recIdents;
            return ;
          }
        } else if (_source153.is_BitwiseNot) {
          DAST.Format._IUnaryOpFormat _3385_format = _3379___mcc_h39;
          DAST._IExpression _3386_e = _3378___mcc_h38;
          {
            RAST._IExpr _3387_recursiveGen;
            DCOMP._IOwnership _3388___v110;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3389_recIdents;
            RAST._IExpr _out1387;
            DCOMP._IOwnership _out1388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1389;
            (this).GenExpr(_3386_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1387, out _out1388, out _out1389);
            _3387_recursiveGen = _out1387;
            _3388___v110 = _out1388;
            _3389_recIdents = _out1389;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _3387_recursiveGen, _3385_format);
            RAST._IExpr _out1390;
            DCOMP._IOwnership _out1391;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1390, out _out1391);
            r = _out1390;
            resultingOwnership = _out1391;
            readIdents = _3389_recIdents;
            return ;
          }
        } else {
          DAST.Format._IUnaryOpFormat _3390_format = _3379___mcc_h39;
          DAST._IExpression _3391_e = _3378___mcc_h38;
          {
            RAST._IExpr _3392_recursiveGen;
            DCOMP._IOwnership _3393_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3394_recIdents;
            RAST._IExpr _out1392;
            DCOMP._IOwnership _out1393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1394;
            (this).GenExpr(_3391_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1392, out _out1393, out _out1394);
            _3392_recursiveGen = _out1392;
            _3393_recOwned = _out1393;
            _3394_recIdents = _out1394;
            r = ((_3392_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1395;
            DCOMP._IOwnership _out1396;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1395, out _out1396);
            r = _out1395;
            resultingOwnership = _out1396;
            readIdents = _3394_recIdents;
            return ;
          }
        }
      } else if (_source151.is_BinOp) {
        DAST._IBinOp _3395___mcc_h40 = _source151.dtor_op;
        DAST._IExpression _3396___mcc_h41 = _source151.dtor_left;
        DAST._IExpression _3397___mcc_h42 = _source151.dtor_right;
        DAST.Format._IBinaryOpFormat _3398___mcc_h43 = _source151.dtor_format2;
        RAST._IExpr _out1397;
        DCOMP._IOwnership _out1398;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1399;
        (this).GenExprBinary(e, selfIdent, @params, expectedOwnership, out _out1397, out _out1398, out _out1399);
        r = _out1397;
        resultingOwnership = _out1398;
        readIdents = _out1399;
      } else if (_source151.is_ArrayLen) {
        DAST._IExpression _3399___mcc_h44 = _source151.dtor_expr;
        BigInteger _3400___mcc_h45 = _source151.dtor_dim;
        BigInteger _3401_dim = _3400___mcc_h45;
        DAST._IExpression _3402_expr = _3399___mcc_h44;
        {
          RAST._IExpr _3403_recursiveGen;
          DCOMP._IOwnership _3404___v115;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3405_recIdents;
          RAST._IExpr _out1400;
          DCOMP._IOwnership _out1401;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1402;
          (this).GenExpr(_3402_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1400, out _out1401, out _out1402);
          _3403_recursiveGen = _out1400;
          _3404___v115 = _out1401;
          _3405_recIdents = _out1402;
          if ((_3401_dim).Sign == 0) {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_3403_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
          } else {
            Dafny.ISequence<Dafny.Rune> _3406_s;
            _3406_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
            BigInteger _3407_i;
            _3407_i = BigInteger.One;
            while ((_3407_i) < (_3401_dim)) {
              _3406_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _3406_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
              _3407_i = (_3407_i) + (BigInteger.One);
            }
            r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_3403_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _3406_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
          }
          RAST._IExpr _out1403;
          DCOMP._IOwnership _out1404;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1403, out _out1404);
          r = _out1403;
          resultingOwnership = _out1404;
          readIdents = _3405_recIdents;
          return ;
        }
      } else if (_source151.is_MapKeys) {
        DAST._IExpression _3408___mcc_h46 = _source151.dtor_expr;
        DAST._IExpression _3409_expr = _3408___mcc_h46;
        {
          RAST._IExpr _3410_recursiveGen;
          DCOMP._IOwnership _3411___v116;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3412_recIdents;
          RAST._IExpr _out1405;
          DCOMP._IOwnership _out1406;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1407;
          (this).GenExpr(_3409_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1405, out _out1406, out _out1407);
          _3410_recursiveGen = _out1405;
          _3411___v116 = _out1406;
          _3412_recIdents = _out1407;
          readIdents = _3412_recIdents;
          r = RAST.Expr.create_Call((_3410_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1408;
          DCOMP._IOwnership _out1409;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1408, out _out1409);
          r = _out1408;
          resultingOwnership = _out1409;
          return ;
        }
      } else if (_source151.is_MapValues) {
        DAST._IExpression _3413___mcc_h47 = _source151.dtor_expr;
        DAST._IExpression _3414_expr = _3413___mcc_h47;
        {
          RAST._IExpr _3415_recursiveGen;
          DCOMP._IOwnership _3416___v117;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3417_recIdents;
          RAST._IExpr _out1410;
          DCOMP._IOwnership _out1411;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1412;
          (this).GenExpr(_3414_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1410, out _out1411, out _out1412);
          _3415_recursiveGen = _out1410;
          _3416___v117 = _out1411;
          _3417_recIdents = _out1412;
          readIdents = _3417_recIdents;
          r = RAST.Expr.create_Call((_3415_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1413;
          DCOMP._IOwnership _out1414;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1413, out _out1414);
          r = _out1413;
          resultingOwnership = _out1414;
          return ;
        }
      } else if (_source151.is_Select) {
        DAST._IExpression _3418___mcc_h48 = _source151.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _3419___mcc_h49 = _source151.dtor_field;
        bool _3420___mcc_h50 = _source151.dtor_isConstant;
        bool _3421___mcc_h51 = _source151.dtor_onDatatype;
        DAST._IExpression _source154 = _3418___mcc_h48;
        if (_source154.is_Literal) {
          DAST._ILiteral _3422___mcc_h52 = _source154.dtor_Literal_a0;
          bool _3423_isDatatype = _3421___mcc_h51;
          bool _3424_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3425_field = _3419___mcc_h49;
          DAST._IExpression _3426_on = _3418___mcc_h48;
          {
            RAST._IExpr _3427_onExpr;
            DCOMP._IOwnership _3428_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3429_recIdents;
            RAST._IExpr _out1415;
            DCOMP._IOwnership _out1416;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1417;
            (this).GenExpr(_3426_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1415, out _out1416, out _out1417);
            _3427_onExpr = _out1415;
            _3428_onOwned = _out1416;
            _3429_recIdents = _out1417;
            if ((_3423_isDatatype) || (_3424_isConstant)) {
              r = RAST.Expr.create_Call((_3427_onExpr).Sel(DCOMP.__default.escapeIdent(_3425_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1418;
              DCOMP._IOwnership _out1419;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1418, out _out1419);
              r = _out1418;
              resultingOwnership = _out1419;
            } else {
              Dafny.ISequence<Dafny.Rune> _3430_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3430_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3427_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3425_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1420;
              DCOMP._IOwnership _out1421;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3430_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1420, out _out1421);
              r = _out1420;
              resultingOwnership = _out1421;
            }
            readIdents = _3429_recIdents;
            return ;
          }
        } else if (_source154.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _3431___mcc_h54 = _source154.dtor_Ident_a0;
          bool _3432_isDatatype = _3421___mcc_h51;
          bool _3433_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3434_field = _3419___mcc_h49;
          DAST._IExpression _3435_on = _3418___mcc_h48;
          {
            RAST._IExpr _3436_onExpr;
            DCOMP._IOwnership _3437_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3438_recIdents;
            RAST._IExpr _out1422;
            DCOMP._IOwnership _out1423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1424;
            (this).GenExpr(_3435_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1422, out _out1423, out _out1424);
            _3436_onExpr = _out1422;
            _3437_onOwned = _out1423;
            _3438_recIdents = _out1424;
            if ((_3432_isDatatype) || (_3433_isConstant)) {
              r = RAST.Expr.create_Call((_3436_onExpr).Sel(DCOMP.__default.escapeIdent(_3434_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1425;
              DCOMP._IOwnership _out1426;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1425, out _out1426);
              r = _out1425;
              resultingOwnership = _out1426;
            } else {
              Dafny.ISequence<Dafny.Rune> _3439_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3439_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3436_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3434_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1427;
              DCOMP._IOwnership _out1428;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3439_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1427, out _out1428);
              r = _out1427;
              resultingOwnership = _out1428;
            }
            readIdents = _3438_recIdents;
            return ;
          }
        } else if (_source154.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3440___mcc_h56 = _source154.dtor_Companion_a0;
          bool _3441_isDatatype = _3421___mcc_h51;
          bool _3442_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3443_field = _3419___mcc_h49;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3444_c = _3440___mcc_h56;
          {
            RAST._IExpr _3445_onExpr;
            DCOMP._IOwnership _3446_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3447_recIdents;
            RAST._IExpr _out1429;
            DCOMP._IOwnership _out1430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1431;
            (this).GenExpr(DAST.Expression.create_Companion(_3444_c), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1429, out _out1430, out _out1431);
            _3445_onExpr = _out1429;
            _3446_onOwned = _out1430;
            _3447_recIdents = _out1431;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_3445_onExpr)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_3443_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")));
            RAST._IExpr _out1432;
            DCOMP._IOwnership _out1433;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1432, out _out1433);
            r = _out1432;
            resultingOwnership = _out1433;
            readIdents = _3447_recIdents;
            return ;
          }
        } else if (_source154.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _3448___mcc_h58 = _source154.dtor_Tuple_a0;
          bool _3449_isDatatype = _3421___mcc_h51;
          bool _3450_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3451_field = _3419___mcc_h49;
          DAST._IExpression _3452_on = _3418___mcc_h48;
          {
            RAST._IExpr _3453_onExpr;
            DCOMP._IOwnership _3454_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3455_recIdents;
            RAST._IExpr _out1434;
            DCOMP._IOwnership _out1435;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1436;
            (this).GenExpr(_3452_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1434, out _out1435, out _out1436);
            _3453_onExpr = _out1434;
            _3454_onOwned = _out1435;
            _3455_recIdents = _out1436;
            if ((_3449_isDatatype) || (_3450_isConstant)) {
              r = RAST.Expr.create_Call((_3453_onExpr).Sel(DCOMP.__default.escapeIdent(_3451_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1437;
              DCOMP._IOwnership _out1438;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1437, out _out1438);
              r = _out1437;
              resultingOwnership = _out1438;
            } else {
              Dafny.ISequence<Dafny.Rune> _3456_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3456_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3453_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3451_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1439;
              DCOMP._IOwnership _out1440;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3456_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1439, out _out1440);
              r = _out1439;
              resultingOwnership = _out1440;
            }
            readIdents = _3455_recIdents;
            return ;
          }
        } else if (_source154.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3457___mcc_h60 = _source154.dtor_path;
          Dafny.ISequence<DAST._IType> _3458___mcc_h61 = _source154.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _3459___mcc_h62 = _source154.dtor_args;
          bool _3460_isDatatype = _3421___mcc_h51;
          bool _3461_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3462_field = _3419___mcc_h49;
          DAST._IExpression _3463_on = _3418___mcc_h48;
          {
            RAST._IExpr _3464_onExpr;
            DCOMP._IOwnership _3465_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3466_recIdents;
            RAST._IExpr _out1441;
            DCOMP._IOwnership _out1442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1443;
            (this).GenExpr(_3463_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1441, out _out1442, out _out1443);
            _3464_onExpr = _out1441;
            _3465_onOwned = _out1442;
            _3466_recIdents = _out1443;
            if ((_3460_isDatatype) || (_3461_isConstant)) {
              r = RAST.Expr.create_Call((_3464_onExpr).Sel(DCOMP.__default.escapeIdent(_3462_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1444;
              DCOMP._IOwnership _out1445;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1444, out _out1445);
              r = _out1444;
              resultingOwnership = _out1445;
            } else {
              Dafny.ISequence<Dafny.Rune> _3467_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3467_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3464_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3462_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1446;
              DCOMP._IOwnership _out1447;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3467_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1446, out _out1447);
              r = _out1446;
              resultingOwnership = _out1447;
            }
            readIdents = _3466_recIdents;
            return ;
          }
        } else if (_source154.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _3468___mcc_h66 = _source154.dtor_dims;
          DAST._IType _3469___mcc_h67 = _source154.dtor_typ;
          bool _3470_isDatatype = _3421___mcc_h51;
          bool _3471_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3472_field = _3419___mcc_h49;
          DAST._IExpression _3473_on = _3418___mcc_h48;
          {
            RAST._IExpr _3474_onExpr;
            DCOMP._IOwnership _3475_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3476_recIdents;
            RAST._IExpr _out1448;
            DCOMP._IOwnership _out1449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1450;
            (this).GenExpr(_3473_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1448, out _out1449, out _out1450);
            _3474_onExpr = _out1448;
            _3475_onOwned = _out1449;
            _3476_recIdents = _out1450;
            if ((_3470_isDatatype) || (_3471_isConstant)) {
              r = RAST.Expr.create_Call((_3474_onExpr).Sel(DCOMP.__default.escapeIdent(_3472_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1451;
              DCOMP._IOwnership _out1452;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1451, out _out1452);
              r = _out1451;
              resultingOwnership = _out1452;
            } else {
              Dafny.ISequence<Dafny.Rune> _3477_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3477_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3474_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3472_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1453;
              DCOMP._IOwnership _out1454;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3477_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1453, out _out1454);
              r = _out1453;
              resultingOwnership = _out1454;
            }
            readIdents = _3476_recIdents;
            return ;
          }
        } else if (_source154.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3478___mcc_h70 = _source154.dtor_path;
          Dafny.ISequence<DAST._IType> _3479___mcc_h71 = _source154.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _3480___mcc_h72 = _source154.dtor_variant;
          bool _3481___mcc_h73 = _source154.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3482___mcc_h74 = _source154.dtor_contents;
          bool _3483_isDatatype = _3421___mcc_h51;
          bool _3484_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3485_field = _3419___mcc_h49;
          DAST._IExpression _3486_on = _3418___mcc_h48;
          {
            RAST._IExpr _3487_onExpr;
            DCOMP._IOwnership _3488_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3489_recIdents;
            RAST._IExpr _out1455;
            DCOMP._IOwnership _out1456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1457;
            (this).GenExpr(_3486_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1455, out _out1456, out _out1457);
            _3487_onExpr = _out1455;
            _3488_onOwned = _out1456;
            _3489_recIdents = _out1457;
            if ((_3483_isDatatype) || (_3484_isConstant)) {
              r = RAST.Expr.create_Call((_3487_onExpr).Sel(DCOMP.__default.escapeIdent(_3485_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1458;
              DCOMP._IOwnership _out1459;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1458, out _out1459);
              r = _out1458;
              resultingOwnership = _out1459;
            } else {
              Dafny.ISequence<Dafny.Rune> _3490_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3490_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3487_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3485_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1460;
              DCOMP._IOwnership _out1461;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3490_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1460, out _out1461);
              r = _out1460;
              resultingOwnership = _out1461;
            }
            readIdents = _3489_recIdents;
            return ;
          }
        } else if (_source154.is_Convert) {
          DAST._IExpression _3491___mcc_h80 = _source154.dtor_value;
          DAST._IType _3492___mcc_h81 = _source154.dtor_from;
          DAST._IType _3493___mcc_h82 = _source154.dtor_typ;
          bool _3494_isDatatype = _3421___mcc_h51;
          bool _3495_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3496_field = _3419___mcc_h49;
          DAST._IExpression _3497_on = _3418___mcc_h48;
          {
            RAST._IExpr _3498_onExpr;
            DCOMP._IOwnership _3499_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3500_recIdents;
            RAST._IExpr _out1462;
            DCOMP._IOwnership _out1463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1464;
            (this).GenExpr(_3497_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1462, out _out1463, out _out1464);
            _3498_onExpr = _out1462;
            _3499_onOwned = _out1463;
            _3500_recIdents = _out1464;
            if ((_3494_isDatatype) || (_3495_isConstant)) {
              r = RAST.Expr.create_Call((_3498_onExpr).Sel(DCOMP.__default.escapeIdent(_3496_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1465;
              DCOMP._IOwnership _out1466;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1465, out _out1466);
              r = _out1465;
              resultingOwnership = _out1466;
            } else {
              Dafny.ISequence<Dafny.Rune> _3501_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3501_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3498_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3496_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1467;
              DCOMP._IOwnership _out1468;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3501_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1467, out _out1468);
              r = _out1467;
              resultingOwnership = _out1468;
            }
            readIdents = _3500_recIdents;
            return ;
          }
        } else if (_source154.is_SeqConstruct) {
          DAST._IExpression _3502___mcc_h86 = _source154.dtor_length;
          DAST._IExpression _3503___mcc_h87 = _source154.dtor_elem;
          bool _3504_isDatatype = _3421___mcc_h51;
          bool _3505_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3506_field = _3419___mcc_h49;
          DAST._IExpression _3507_on = _3418___mcc_h48;
          {
            RAST._IExpr _3508_onExpr;
            DCOMP._IOwnership _3509_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3510_recIdents;
            RAST._IExpr _out1469;
            DCOMP._IOwnership _out1470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1471;
            (this).GenExpr(_3507_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1469, out _out1470, out _out1471);
            _3508_onExpr = _out1469;
            _3509_onOwned = _out1470;
            _3510_recIdents = _out1471;
            if ((_3504_isDatatype) || (_3505_isConstant)) {
              r = RAST.Expr.create_Call((_3508_onExpr).Sel(DCOMP.__default.escapeIdent(_3506_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1472;
              DCOMP._IOwnership _out1473;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1472, out _out1473);
              r = _out1472;
              resultingOwnership = _out1473;
            } else {
              Dafny.ISequence<Dafny.Rune> _3511_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3511_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3508_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3506_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1474;
              DCOMP._IOwnership _out1475;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3511_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1474, out _out1475);
              r = _out1474;
              resultingOwnership = _out1475;
            }
            readIdents = _3510_recIdents;
            return ;
          }
        } else if (_source154.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _3512___mcc_h90 = _source154.dtor_elements;
          DAST._IType _3513___mcc_h91 = _source154.dtor_typ;
          bool _3514_isDatatype = _3421___mcc_h51;
          bool _3515_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3516_field = _3419___mcc_h49;
          DAST._IExpression _3517_on = _3418___mcc_h48;
          {
            RAST._IExpr _3518_onExpr;
            DCOMP._IOwnership _3519_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3520_recIdents;
            RAST._IExpr _out1476;
            DCOMP._IOwnership _out1477;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1478;
            (this).GenExpr(_3517_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1476, out _out1477, out _out1478);
            _3518_onExpr = _out1476;
            _3519_onOwned = _out1477;
            _3520_recIdents = _out1478;
            if ((_3514_isDatatype) || (_3515_isConstant)) {
              r = RAST.Expr.create_Call((_3518_onExpr).Sel(DCOMP.__default.escapeIdent(_3516_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1479;
              DCOMP._IOwnership _out1480;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1479, out _out1480);
              r = _out1479;
              resultingOwnership = _out1480;
            } else {
              Dafny.ISequence<Dafny.Rune> _3521_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3521_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3518_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3516_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1481;
              DCOMP._IOwnership _out1482;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3521_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1481, out _out1482);
              r = _out1481;
              resultingOwnership = _out1482;
            }
            readIdents = _3520_recIdents;
            return ;
          }
        } else if (_source154.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _3522___mcc_h94 = _source154.dtor_elements;
          bool _3523_isDatatype = _3421___mcc_h51;
          bool _3524_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3525_field = _3419___mcc_h49;
          DAST._IExpression _3526_on = _3418___mcc_h48;
          {
            RAST._IExpr _3527_onExpr;
            DCOMP._IOwnership _3528_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3529_recIdents;
            RAST._IExpr _out1483;
            DCOMP._IOwnership _out1484;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1485;
            (this).GenExpr(_3526_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1483, out _out1484, out _out1485);
            _3527_onExpr = _out1483;
            _3528_onOwned = _out1484;
            _3529_recIdents = _out1485;
            if ((_3523_isDatatype) || (_3524_isConstant)) {
              r = RAST.Expr.create_Call((_3527_onExpr).Sel(DCOMP.__default.escapeIdent(_3525_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1486;
              DCOMP._IOwnership _out1487;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1486, out _out1487);
              r = _out1486;
              resultingOwnership = _out1487;
            } else {
              Dafny.ISequence<Dafny.Rune> _3530_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3530_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3527_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3525_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1488;
              DCOMP._IOwnership _out1489;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3530_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1488, out _out1489);
              r = _out1488;
              resultingOwnership = _out1489;
            }
            readIdents = _3529_recIdents;
            return ;
          }
        } else if (_source154.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _3531___mcc_h96 = _source154.dtor_elements;
          bool _3532_isDatatype = _3421___mcc_h51;
          bool _3533_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3534_field = _3419___mcc_h49;
          DAST._IExpression _3535_on = _3418___mcc_h48;
          {
            RAST._IExpr _3536_onExpr;
            DCOMP._IOwnership _3537_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3538_recIdents;
            RAST._IExpr _out1490;
            DCOMP._IOwnership _out1491;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1492;
            (this).GenExpr(_3535_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1490, out _out1491, out _out1492);
            _3536_onExpr = _out1490;
            _3537_onOwned = _out1491;
            _3538_recIdents = _out1492;
            if ((_3532_isDatatype) || (_3533_isConstant)) {
              r = RAST.Expr.create_Call((_3536_onExpr).Sel(DCOMP.__default.escapeIdent(_3534_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1493;
              DCOMP._IOwnership _out1494;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1493, out _out1494);
              r = _out1493;
              resultingOwnership = _out1494;
            } else {
              Dafny.ISequence<Dafny.Rune> _3539_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3539_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3536_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3534_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1495;
              DCOMP._IOwnership _out1496;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3539_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1495, out _out1496);
              r = _out1495;
              resultingOwnership = _out1496;
            }
            readIdents = _3538_recIdents;
            return ;
          }
        } else if (_source154.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3540___mcc_h98 = _source154.dtor_mapElems;
          bool _3541_isDatatype = _3421___mcc_h51;
          bool _3542_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3543_field = _3419___mcc_h49;
          DAST._IExpression _3544_on = _3418___mcc_h48;
          {
            RAST._IExpr _3545_onExpr;
            DCOMP._IOwnership _3546_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3547_recIdents;
            RAST._IExpr _out1497;
            DCOMP._IOwnership _out1498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1499;
            (this).GenExpr(_3544_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1497, out _out1498, out _out1499);
            _3545_onExpr = _out1497;
            _3546_onOwned = _out1498;
            _3547_recIdents = _out1499;
            if ((_3541_isDatatype) || (_3542_isConstant)) {
              r = RAST.Expr.create_Call((_3545_onExpr).Sel(DCOMP.__default.escapeIdent(_3543_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1500;
              DCOMP._IOwnership _out1501;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1500, out _out1501);
              r = _out1500;
              resultingOwnership = _out1501;
            } else {
              Dafny.ISequence<Dafny.Rune> _3548_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3548_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3545_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3543_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1502;
              DCOMP._IOwnership _out1503;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3548_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1502, out _out1503);
              r = _out1502;
              resultingOwnership = _out1503;
            }
            readIdents = _3547_recIdents;
            return ;
          }
        } else if (_source154.is_MapBuilder) {
          DAST._IType _3549___mcc_h100 = _source154.dtor_keyType;
          DAST._IType _3550___mcc_h101 = _source154.dtor_valueType;
          bool _3551_isDatatype = _3421___mcc_h51;
          bool _3552_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3553_field = _3419___mcc_h49;
          DAST._IExpression _3554_on = _3418___mcc_h48;
          {
            RAST._IExpr _3555_onExpr;
            DCOMP._IOwnership _3556_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3557_recIdents;
            RAST._IExpr _out1504;
            DCOMP._IOwnership _out1505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1506;
            (this).GenExpr(_3554_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1504, out _out1505, out _out1506);
            _3555_onExpr = _out1504;
            _3556_onOwned = _out1505;
            _3557_recIdents = _out1506;
            if ((_3551_isDatatype) || (_3552_isConstant)) {
              r = RAST.Expr.create_Call((_3555_onExpr).Sel(DCOMP.__default.escapeIdent(_3553_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1507;
              DCOMP._IOwnership _out1508;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1507, out _out1508);
              r = _out1507;
              resultingOwnership = _out1508;
            } else {
              Dafny.ISequence<Dafny.Rune> _3558_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3558_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3555_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3553_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1509;
              DCOMP._IOwnership _out1510;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3558_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1509, out _out1510);
              r = _out1509;
              resultingOwnership = _out1510;
            }
            readIdents = _3557_recIdents;
            return ;
          }
        } else if (_source154.is_SeqUpdate) {
          DAST._IExpression _3559___mcc_h104 = _source154.dtor_expr;
          DAST._IExpression _3560___mcc_h105 = _source154.dtor_indexExpr;
          DAST._IExpression _3561___mcc_h106 = _source154.dtor_value;
          bool _3562_isDatatype = _3421___mcc_h51;
          bool _3563_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3564_field = _3419___mcc_h49;
          DAST._IExpression _3565_on = _3418___mcc_h48;
          {
            RAST._IExpr _3566_onExpr;
            DCOMP._IOwnership _3567_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3568_recIdents;
            RAST._IExpr _out1511;
            DCOMP._IOwnership _out1512;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1513;
            (this).GenExpr(_3565_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1511, out _out1512, out _out1513);
            _3566_onExpr = _out1511;
            _3567_onOwned = _out1512;
            _3568_recIdents = _out1513;
            if ((_3562_isDatatype) || (_3563_isConstant)) {
              r = RAST.Expr.create_Call((_3566_onExpr).Sel(DCOMP.__default.escapeIdent(_3564_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1514;
              DCOMP._IOwnership _out1515;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1514, out _out1515);
              r = _out1514;
              resultingOwnership = _out1515;
            } else {
              Dafny.ISequence<Dafny.Rune> _3569_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3569_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3566_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3564_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1516;
              DCOMP._IOwnership _out1517;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3569_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1516, out _out1517);
              r = _out1516;
              resultingOwnership = _out1517;
            }
            readIdents = _3568_recIdents;
            return ;
          }
        } else if (_source154.is_MapUpdate) {
          DAST._IExpression _3570___mcc_h110 = _source154.dtor_expr;
          DAST._IExpression _3571___mcc_h111 = _source154.dtor_indexExpr;
          DAST._IExpression _3572___mcc_h112 = _source154.dtor_value;
          bool _3573_isDatatype = _3421___mcc_h51;
          bool _3574_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3575_field = _3419___mcc_h49;
          DAST._IExpression _3576_on = _3418___mcc_h48;
          {
            RAST._IExpr _3577_onExpr;
            DCOMP._IOwnership _3578_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3579_recIdents;
            RAST._IExpr _out1518;
            DCOMP._IOwnership _out1519;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1520;
            (this).GenExpr(_3576_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1518, out _out1519, out _out1520);
            _3577_onExpr = _out1518;
            _3578_onOwned = _out1519;
            _3579_recIdents = _out1520;
            if ((_3573_isDatatype) || (_3574_isConstant)) {
              r = RAST.Expr.create_Call((_3577_onExpr).Sel(DCOMP.__default.escapeIdent(_3575_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1521;
              DCOMP._IOwnership _out1522;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1521, out _out1522);
              r = _out1521;
              resultingOwnership = _out1522;
            } else {
              Dafny.ISequence<Dafny.Rune> _3580_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3580_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3577_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3575_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1523;
              DCOMP._IOwnership _out1524;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3580_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1523, out _out1524);
              r = _out1523;
              resultingOwnership = _out1524;
            }
            readIdents = _3579_recIdents;
            return ;
          }
        } else if (_source154.is_SetBuilder) {
          DAST._IType _3581___mcc_h116 = _source154.dtor_elemType;
          bool _3582_isDatatype = _3421___mcc_h51;
          bool _3583_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3584_field = _3419___mcc_h49;
          DAST._IExpression _3585_on = _3418___mcc_h48;
          {
            RAST._IExpr _3586_onExpr;
            DCOMP._IOwnership _3587_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3588_recIdents;
            RAST._IExpr _out1525;
            DCOMP._IOwnership _out1526;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1527;
            (this).GenExpr(_3585_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1525, out _out1526, out _out1527);
            _3586_onExpr = _out1525;
            _3587_onOwned = _out1526;
            _3588_recIdents = _out1527;
            if ((_3582_isDatatype) || (_3583_isConstant)) {
              r = RAST.Expr.create_Call((_3586_onExpr).Sel(DCOMP.__default.escapeIdent(_3584_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1528;
              DCOMP._IOwnership _out1529;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1528, out _out1529);
              r = _out1528;
              resultingOwnership = _out1529;
            } else {
              Dafny.ISequence<Dafny.Rune> _3589_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3589_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3586_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3584_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1530;
              DCOMP._IOwnership _out1531;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3589_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1530, out _out1531);
              r = _out1530;
              resultingOwnership = _out1531;
            }
            readIdents = _3588_recIdents;
            return ;
          }
        } else if (_source154.is_ToMultiset) {
          DAST._IExpression _3590___mcc_h118 = _source154.dtor_ToMultiset_a0;
          bool _3591_isDatatype = _3421___mcc_h51;
          bool _3592_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3593_field = _3419___mcc_h49;
          DAST._IExpression _3594_on = _3418___mcc_h48;
          {
            RAST._IExpr _3595_onExpr;
            DCOMP._IOwnership _3596_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3597_recIdents;
            RAST._IExpr _out1532;
            DCOMP._IOwnership _out1533;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1534;
            (this).GenExpr(_3594_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1532, out _out1533, out _out1534);
            _3595_onExpr = _out1532;
            _3596_onOwned = _out1533;
            _3597_recIdents = _out1534;
            if ((_3591_isDatatype) || (_3592_isConstant)) {
              r = RAST.Expr.create_Call((_3595_onExpr).Sel(DCOMP.__default.escapeIdent(_3593_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1535;
              DCOMP._IOwnership _out1536;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1535, out _out1536);
              r = _out1535;
              resultingOwnership = _out1536;
            } else {
              Dafny.ISequence<Dafny.Rune> _3598_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3598_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3595_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3593_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1537;
              DCOMP._IOwnership _out1538;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3598_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1537, out _out1538);
              r = _out1537;
              resultingOwnership = _out1538;
            }
            readIdents = _3597_recIdents;
            return ;
          }
        } else if (_source154.is_This) {
          bool _3599_isDatatype = _3421___mcc_h51;
          bool _3600_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3601_field = _3419___mcc_h49;
          DAST._IExpression _3602_on = _3418___mcc_h48;
          {
            RAST._IExpr _3603_onExpr;
            DCOMP._IOwnership _3604_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3605_recIdents;
            RAST._IExpr _out1539;
            DCOMP._IOwnership _out1540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1541;
            (this).GenExpr(_3602_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1539, out _out1540, out _out1541);
            _3603_onExpr = _out1539;
            _3604_onOwned = _out1540;
            _3605_recIdents = _out1541;
            if ((_3599_isDatatype) || (_3600_isConstant)) {
              r = RAST.Expr.create_Call((_3603_onExpr).Sel(DCOMP.__default.escapeIdent(_3601_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1542;
              DCOMP._IOwnership _out1543;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1542, out _out1543);
              r = _out1542;
              resultingOwnership = _out1543;
            } else {
              Dafny.ISequence<Dafny.Rune> _3606_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3606_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3603_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3601_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1544;
              DCOMP._IOwnership _out1545;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3606_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1544, out _out1545);
              r = _out1544;
              resultingOwnership = _out1545;
            }
            readIdents = _3605_recIdents;
            return ;
          }
        } else if (_source154.is_Ite) {
          DAST._IExpression _3607___mcc_h120 = _source154.dtor_cond;
          DAST._IExpression _3608___mcc_h121 = _source154.dtor_thn;
          DAST._IExpression _3609___mcc_h122 = _source154.dtor_els;
          bool _3610_isDatatype = _3421___mcc_h51;
          bool _3611_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3612_field = _3419___mcc_h49;
          DAST._IExpression _3613_on = _3418___mcc_h48;
          {
            RAST._IExpr _3614_onExpr;
            DCOMP._IOwnership _3615_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3616_recIdents;
            RAST._IExpr _out1546;
            DCOMP._IOwnership _out1547;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1548;
            (this).GenExpr(_3613_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1546, out _out1547, out _out1548);
            _3614_onExpr = _out1546;
            _3615_onOwned = _out1547;
            _3616_recIdents = _out1548;
            if ((_3610_isDatatype) || (_3611_isConstant)) {
              r = RAST.Expr.create_Call((_3614_onExpr).Sel(DCOMP.__default.escapeIdent(_3612_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1549;
              DCOMP._IOwnership _out1550;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1549, out _out1550);
              r = _out1549;
              resultingOwnership = _out1550;
            } else {
              Dafny.ISequence<Dafny.Rune> _3617_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3617_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3614_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3612_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1551;
              DCOMP._IOwnership _out1552;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3617_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1551, out _out1552);
              r = _out1551;
              resultingOwnership = _out1552;
            }
            readIdents = _3616_recIdents;
            return ;
          }
        } else if (_source154.is_UnOp) {
          DAST._IUnaryOp _3618___mcc_h126 = _source154.dtor_unOp;
          DAST._IExpression _3619___mcc_h127 = _source154.dtor_expr;
          DAST.Format._IUnaryOpFormat _3620___mcc_h128 = _source154.dtor_format1;
          bool _3621_isDatatype = _3421___mcc_h51;
          bool _3622_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3623_field = _3419___mcc_h49;
          DAST._IExpression _3624_on = _3418___mcc_h48;
          {
            RAST._IExpr _3625_onExpr;
            DCOMP._IOwnership _3626_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3627_recIdents;
            RAST._IExpr _out1553;
            DCOMP._IOwnership _out1554;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1555;
            (this).GenExpr(_3624_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1553, out _out1554, out _out1555);
            _3625_onExpr = _out1553;
            _3626_onOwned = _out1554;
            _3627_recIdents = _out1555;
            if ((_3621_isDatatype) || (_3622_isConstant)) {
              r = RAST.Expr.create_Call((_3625_onExpr).Sel(DCOMP.__default.escapeIdent(_3623_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1556;
              DCOMP._IOwnership _out1557;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1556, out _out1557);
              r = _out1556;
              resultingOwnership = _out1557;
            } else {
              Dafny.ISequence<Dafny.Rune> _3628_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3628_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3625_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3623_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1558;
              DCOMP._IOwnership _out1559;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3628_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1558, out _out1559);
              r = _out1558;
              resultingOwnership = _out1559;
            }
            readIdents = _3627_recIdents;
            return ;
          }
        } else if (_source154.is_BinOp) {
          DAST._IBinOp _3629___mcc_h132 = _source154.dtor_op;
          DAST._IExpression _3630___mcc_h133 = _source154.dtor_left;
          DAST._IExpression _3631___mcc_h134 = _source154.dtor_right;
          DAST.Format._IBinaryOpFormat _3632___mcc_h135 = _source154.dtor_format2;
          bool _3633_isDatatype = _3421___mcc_h51;
          bool _3634_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3635_field = _3419___mcc_h49;
          DAST._IExpression _3636_on = _3418___mcc_h48;
          {
            RAST._IExpr _3637_onExpr;
            DCOMP._IOwnership _3638_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3639_recIdents;
            RAST._IExpr _out1560;
            DCOMP._IOwnership _out1561;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1562;
            (this).GenExpr(_3636_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1560, out _out1561, out _out1562);
            _3637_onExpr = _out1560;
            _3638_onOwned = _out1561;
            _3639_recIdents = _out1562;
            if ((_3633_isDatatype) || (_3634_isConstant)) {
              r = RAST.Expr.create_Call((_3637_onExpr).Sel(DCOMP.__default.escapeIdent(_3635_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1563;
              DCOMP._IOwnership _out1564;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1563, out _out1564);
              r = _out1563;
              resultingOwnership = _out1564;
            } else {
              Dafny.ISequence<Dafny.Rune> _3640_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3640_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3637_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3635_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1565;
              DCOMP._IOwnership _out1566;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3640_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1565, out _out1566);
              r = _out1565;
              resultingOwnership = _out1566;
            }
            readIdents = _3639_recIdents;
            return ;
          }
        } else if (_source154.is_ArrayLen) {
          DAST._IExpression _3641___mcc_h140 = _source154.dtor_expr;
          BigInteger _3642___mcc_h141 = _source154.dtor_dim;
          bool _3643_isDatatype = _3421___mcc_h51;
          bool _3644_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3645_field = _3419___mcc_h49;
          DAST._IExpression _3646_on = _3418___mcc_h48;
          {
            RAST._IExpr _3647_onExpr;
            DCOMP._IOwnership _3648_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3649_recIdents;
            RAST._IExpr _out1567;
            DCOMP._IOwnership _out1568;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1569;
            (this).GenExpr(_3646_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1567, out _out1568, out _out1569);
            _3647_onExpr = _out1567;
            _3648_onOwned = _out1568;
            _3649_recIdents = _out1569;
            if ((_3643_isDatatype) || (_3644_isConstant)) {
              r = RAST.Expr.create_Call((_3647_onExpr).Sel(DCOMP.__default.escapeIdent(_3645_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1570;
              DCOMP._IOwnership _out1571;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1570, out _out1571);
              r = _out1570;
              resultingOwnership = _out1571;
            } else {
              Dafny.ISequence<Dafny.Rune> _3650_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3650_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3647_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3645_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1572;
              DCOMP._IOwnership _out1573;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3650_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1572, out _out1573);
              r = _out1572;
              resultingOwnership = _out1573;
            }
            readIdents = _3649_recIdents;
            return ;
          }
        } else if (_source154.is_MapKeys) {
          DAST._IExpression _3651___mcc_h144 = _source154.dtor_expr;
          bool _3652_isDatatype = _3421___mcc_h51;
          bool _3653_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3654_field = _3419___mcc_h49;
          DAST._IExpression _3655_on = _3418___mcc_h48;
          {
            RAST._IExpr _3656_onExpr;
            DCOMP._IOwnership _3657_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3658_recIdents;
            RAST._IExpr _out1574;
            DCOMP._IOwnership _out1575;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1576;
            (this).GenExpr(_3655_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1574, out _out1575, out _out1576);
            _3656_onExpr = _out1574;
            _3657_onOwned = _out1575;
            _3658_recIdents = _out1576;
            if ((_3652_isDatatype) || (_3653_isConstant)) {
              r = RAST.Expr.create_Call((_3656_onExpr).Sel(DCOMP.__default.escapeIdent(_3654_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1577;
              DCOMP._IOwnership _out1578;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1577, out _out1578);
              r = _out1577;
              resultingOwnership = _out1578;
            } else {
              Dafny.ISequence<Dafny.Rune> _3659_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3659_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3656_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3654_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1579;
              DCOMP._IOwnership _out1580;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3659_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1579, out _out1580);
              r = _out1579;
              resultingOwnership = _out1580;
            }
            readIdents = _3658_recIdents;
            return ;
          }
        } else if (_source154.is_MapValues) {
          DAST._IExpression _3660___mcc_h146 = _source154.dtor_expr;
          bool _3661_isDatatype = _3421___mcc_h51;
          bool _3662_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3663_field = _3419___mcc_h49;
          DAST._IExpression _3664_on = _3418___mcc_h48;
          {
            RAST._IExpr _3665_onExpr;
            DCOMP._IOwnership _3666_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3667_recIdents;
            RAST._IExpr _out1581;
            DCOMP._IOwnership _out1582;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1583;
            (this).GenExpr(_3664_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1581, out _out1582, out _out1583);
            _3665_onExpr = _out1581;
            _3666_onOwned = _out1582;
            _3667_recIdents = _out1583;
            if ((_3661_isDatatype) || (_3662_isConstant)) {
              r = RAST.Expr.create_Call((_3665_onExpr).Sel(DCOMP.__default.escapeIdent(_3663_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1584;
              DCOMP._IOwnership _out1585;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1584, out _out1585);
              r = _out1584;
              resultingOwnership = _out1585;
            } else {
              Dafny.ISequence<Dafny.Rune> _3668_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3668_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3665_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3663_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1586;
              DCOMP._IOwnership _out1587;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3668_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1586, out _out1587);
              r = _out1586;
              resultingOwnership = _out1587;
            }
            readIdents = _3667_recIdents;
            return ;
          }
        } else if (_source154.is_Select) {
          DAST._IExpression _3669___mcc_h148 = _source154.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _3670___mcc_h149 = _source154.dtor_field;
          bool _3671___mcc_h150 = _source154.dtor_isConstant;
          bool _3672___mcc_h151 = _source154.dtor_onDatatype;
          bool _3673_isDatatype = _3421___mcc_h51;
          bool _3674_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3675_field = _3419___mcc_h49;
          DAST._IExpression _3676_on = _3418___mcc_h48;
          {
            RAST._IExpr _3677_onExpr;
            DCOMP._IOwnership _3678_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3679_recIdents;
            RAST._IExpr _out1588;
            DCOMP._IOwnership _out1589;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1590;
            (this).GenExpr(_3676_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1588, out _out1589, out _out1590);
            _3677_onExpr = _out1588;
            _3678_onOwned = _out1589;
            _3679_recIdents = _out1590;
            if ((_3673_isDatatype) || (_3674_isConstant)) {
              r = RAST.Expr.create_Call((_3677_onExpr).Sel(DCOMP.__default.escapeIdent(_3675_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1591;
              DCOMP._IOwnership _out1592;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1591, out _out1592);
              r = _out1591;
              resultingOwnership = _out1592;
            } else {
              Dafny.ISequence<Dafny.Rune> _3680_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3680_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3677_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3675_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1593;
              DCOMP._IOwnership _out1594;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3680_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1593, out _out1594);
              r = _out1593;
              resultingOwnership = _out1594;
            }
            readIdents = _3679_recIdents;
            return ;
          }
        } else if (_source154.is_SelectFn) {
          DAST._IExpression _3681___mcc_h156 = _source154.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _3682___mcc_h157 = _source154.dtor_field;
          bool _3683___mcc_h158 = _source154.dtor_onDatatype;
          bool _3684___mcc_h159 = _source154.dtor_isStatic;
          BigInteger _3685___mcc_h160 = _source154.dtor_arity;
          bool _3686_isDatatype = _3421___mcc_h51;
          bool _3687_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3688_field = _3419___mcc_h49;
          DAST._IExpression _3689_on = _3418___mcc_h48;
          {
            RAST._IExpr _3690_onExpr;
            DCOMP._IOwnership _3691_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3692_recIdents;
            RAST._IExpr _out1595;
            DCOMP._IOwnership _out1596;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1597;
            (this).GenExpr(_3689_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1595, out _out1596, out _out1597);
            _3690_onExpr = _out1595;
            _3691_onOwned = _out1596;
            _3692_recIdents = _out1597;
            if ((_3686_isDatatype) || (_3687_isConstant)) {
              r = RAST.Expr.create_Call((_3690_onExpr).Sel(DCOMP.__default.escapeIdent(_3688_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1598;
              DCOMP._IOwnership _out1599;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1598, out _out1599);
              r = _out1598;
              resultingOwnership = _out1599;
            } else {
              Dafny.ISequence<Dafny.Rune> _3693_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3693_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3690_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3688_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1600;
              DCOMP._IOwnership _out1601;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3693_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1600, out _out1601);
              r = _out1600;
              resultingOwnership = _out1601;
            }
            readIdents = _3692_recIdents;
            return ;
          }
        } else if (_source154.is_Index) {
          DAST._IExpression _3694___mcc_h166 = _source154.dtor_expr;
          DAST._ICollKind _3695___mcc_h167 = _source154.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _3696___mcc_h168 = _source154.dtor_indices;
          bool _3697_isDatatype = _3421___mcc_h51;
          bool _3698_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3699_field = _3419___mcc_h49;
          DAST._IExpression _3700_on = _3418___mcc_h48;
          {
            RAST._IExpr _3701_onExpr;
            DCOMP._IOwnership _3702_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3703_recIdents;
            RAST._IExpr _out1602;
            DCOMP._IOwnership _out1603;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1604;
            (this).GenExpr(_3700_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1602, out _out1603, out _out1604);
            _3701_onExpr = _out1602;
            _3702_onOwned = _out1603;
            _3703_recIdents = _out1604;
            if ((_3697_isDatatype) || (_3698_isConstant)) {
              r = RAST.Expr.create_Call((_3701_onExpr).Sel(DCOMP.__default.escapeIdent(_3699_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1605;
              DCOMP._IOwnership _out1606;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1605, out _out1606);
              r = _out1605;
              resultingOwnership = _out1606;
            } else {
              Dafny.ISequence<Dafny.Rune> _3704_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3704_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3701_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3699_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1607;
              DCOMP._IOwnership _out1608;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3704_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1607, out _out1608);
              r = _out1607;
              resultingOwnership = _out1608;
            }
            readIdents = _3703_recIdents;
            return ;
          }
        } else if (_source154.is_IndexRange) {
          DAST._IExpression _3705___mcc_h172 = _source154.dtor_expr;
          bool _3706___mcc_h173 = _source154.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _3707___mcc_h174 = _source154.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _3708___mcc_h175 = _source154.dtor_high;
          bool _3709_isDatatype = _3421___mcc_h51;
          bool _3710_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3711_field = _3419___mcc_h49;
          DAST._IExpression _3712_on = _3418___mcc_h48;
          {
            RAST._IExpr _3713_onExpr;
            DCOMP._IOwnership _3714_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3715_recIdents;
            RAST._IExpr _out1609;
            DCOMP._IOwnership _out1610;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1611;
            (this).GenExpr(_3712_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1609, out _out1610, out _out1611);
            _3713_onExpr = _out1609;
            _3714_onOwned = _out1610;
            _3715_recIdents = _out1611;
            if ((_3709_isDatatype) || (_3710_isConstant)) {
              r = RAST.Expr.create_Call((_3713_onExpr).Sel(DCOMP.__default.escapeIdent(_3711_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1612;
              DCOMP._IOwnership _out1613;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1612, out _out1613);
              r = _out1612;
              resultingOwnership = _out1613;
            } else {
              Dafny.ISequence<Dafny.Rune> _3716_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3716_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3713_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3711_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1614;
              DCOMP._IOwnership _out1615;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3716_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1614, out _out1615);
              r = _out1614;
              resultingOwnership = _out1615;
            }
            readIdents = _3715_recIdents;
            return ;
          }
        } else if (_source154.is_TupleSelect) {
          DAST._IExpression _3717___mcc_h180 = _source154.dtor_expr;
          BigInteger _3718___mcc_h181 = _source154.dtor_index;
          bool _3719_isDatatype = _3421___mcc_h51;
          bool _3720_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3721_field = _3419___mcc_h49;
          DAST._IExpression _3722_on = _3418___mcc_h48;
          {
            RAST._IExpr _3723_onExpr;
            DCOMP._IOwnership _3724_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3725_recIdents;
            RAST._IExpr _out1616;
            DCOMP._IOwnership _out1617;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1618;
            (this).GenExpr(_3722_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1616, out _out1617, out _out1618);
            _3723_onExpr = _out1616;
            _3724_onOwned = _out1617;
            _3725_recIdents = _out1618;
            if ((_3719_isDatatype) || (_3720_isConstant)) {
              r = RAST.Expr.create_Call((_3723_onExpr).Sel(DCOMP.__default.escapeIdent(_3721_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1619;
              DCOMP._IOwnership _out1620;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1619, out _out1620);
              r = _out1619;
              resultingOwnership = _out1620;
            } else {
              Dafny.ISequence<Dafny.Rune> _3726_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3726_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3723_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3721_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1621;
              DCOMP._IOwnership _out1622;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3726_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1621, out _out1622);
              r = _out1621;
              resultingOwnership = _out1622;
            }
            readIdents = _3725_recIdents;
            return ;
          }
        } else if (_source154.is_Call) {
          DAST._IExpression _3727___mcc_h184 = _source154.dtor_on;
          DAST._ICallName _3728___mcc_h185 = _source154.dtor_callName;
          Dafny.ISequence<DAST._IType> _3729___mcc_h186 = _source154.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _3730___mcc_h187 = _source154.dtor_args;
          bool _3731_isDatatype = _3421___mcc_h51;
          bool _3732_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3733_field = _3419___mcc_h49;
          DAST._IExpression _3734_on = _3418___mcc_h48;
          {
            RAST._IExpr _3735_onExpr;
            DCOMP._IOwnership _3736_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3737_recIdents;
            RAST._IExpr _out1623;
            DCOMP._IOwnership _out1624;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1625;
            (this).GenExpr(_3734_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1623, out _out1624, out _out1625);
            _3735_onExpr = _out1623;
            _3736_onOwned = _out1624;
            _3737_recIdents = _out1625;
            if ((_3731_isDatatype) || (_3732_isConstant)) {
              r = RAST.Expr.create_Call((_3735_onExpr).Sel(DCOMP.__default.escapeIdent(_3733_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1626;
              DCOMP._IOwnership _out1627;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1626, out _out1627);
              r = _out1626;
              resultingOwnership = _out1627;
            } else {
              Dafny.ISequence<Dafny.Rune> _3738_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3738_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3735_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3733_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1628;
              DCOMP._IOwnership _out1629;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3738_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1628, out _out1629);
              r = _out1628;
              resultingOwnership = _out1629;
            }
            readIdents = _3737_recIdents;
            return ;
          }
        } else if (_source154.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _3739___mcc_h192 = _source154.dtor_params;
          DAST._IType _3740___mcc_h193 = _source154.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _3741___mcc_h194 = _source154.dtor_body;
          bool _3742_isDatatype = _3421___mcc_h51;
          bool _3743_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3744_field = _3419___mcc_h49;
          DAST._IExpression _3745_on = _3418___mcc_h48;
          {
            RAST._IExpr _3746_onExpr;
            DCOMP._IOwnership _3747_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3748_recIdents;
            RAST._IExpr _out1630;
            DCOMP._IOwnership _out1631;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1632;
            (this).GenExpr(_3745_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1630, out _out1631, out _out1632);
            _3746_onExpr = _out1630;
            _3747_onOwned = _out1631;
            _3748_recIdents = _out1632;
            if ((_3742_isDatatype) || (_3743_isConstant)) {
              r = RAST.Expr.create_Call((_3746_onExpr).Sel(DCOMP.__default.escapeIdent(_3744_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1633;
              DCOMP._IOwnership _out1634;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1633, out _out1634);
              r = _out1633;
              resultingOwnership = _out1634;
            } else {
              Dafny.ISequence<Dafny.Rune> _3749_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3749_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3746_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3744_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1635;
              DCOMP._IOwnership _out1636;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3749_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1635, out _out1636);
              r = _out1635;
              resultingOwnership = _out1636;
            }
            readIdents = _3748_recIdents;
            return ;
          }
        } else if (_source154.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _3750___mcc_h198 = _source154.dtor_values;
          DAST._IType _3751___mcc_h199 = _source154.dtor_retType;
          DAST._IExpression _3752___mcc_h200 = _source154.dtor_expr;
          bool _3753_isDatatype = _3421___mcc_h51;
          bool _3754_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3755_field = _3419___mcc_h49;
          DAST._IExpression _3756_on = _3418___mcc_h48;
          {
            RAST._IExpr _3757_onExpr;
            DCOMP._IOwnership _3758_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3759_recIdents;
            RAST._IExpr _out1637;
            DCOMP._IOwnership _out1638;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1639;
            (this).GenExpr(_3756_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1637, out _out1638, out _out1639);
            _3757_onExpr = _out1637;
            _3758_onOwned = _out1638;
            _3759_recIdents = _out1639;
            if ((_3753_isDatatype) || (_3754_isConstant)) {
              r = RAST.Expr.create_Call((_3757_onExpr).Sel(DCOMP.__default.escapeIdent(_3755_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1640;
              DCOMP._IOwnership _out1641;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1640, out _out1641);
              r = _out1640;
              resultingOwnership = _out1641;
            } else {
              Dafny.ISequence<Dafny.Rune> _3760_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3760_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3757_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3755_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1642;
              DCOMP._IOwnership _out1643;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3760_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1642, out _out1643);
              r = _out1642;
              resultingOwnership = _out1643;
            }
            readIdents = _3759_recIdents;
            return ;
          }
        } else if (_source154.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _3761___mcc_h204 = _source154.dtor_name;
          DAST._IType _3762___mcc_h205 = _source154.dtor_typ;
          DAST._IExpression _3763___mcc_h206 = _source154.dtor_value;
          DAST._IExpression _3764___mcc_h207 = _source154.dtor_iifeBody;
          bool _3765_isDatatype = _3421___mcc_h51;
          bool _3766_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3767_field = _3419___mcc_h49;
          DAST._IExpression _3768_on = _3418___mcc_h48;
          {
            RAST._IExpr _3769_onExpr;
            DCOMP._IOwnership _3770_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3771_recIdents;
            RAST._IExpr _out1644;
            DCOMP._IOwnership _out1645;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1646;
            (this).GenExpr(_3768_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1644, out _out1645, out _out1646);
            _3769_onExpr = _out1644;
            _3770_onOwned = _out1645;
            _3771_recIdents = _out1646;
            if ((_3765_isDatatype) || (_3766_isConstant)) {
              r = RAST.Expr.create_Call((_3769_onExpr).Sel(DCOMP.__default.escapeIdent(_3767_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1647;
              DCOMP._IOwnership _out1648;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1647, out _out1648);
              r = _out1647;
              resultingOwnership = _out1648;
            } else {
              Dafny.ISequence<Dafny.Rune> _3772_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3772_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3769_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3767_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1649;
              DCOMP._IOwnership _out1650;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3772_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1649, out _out1650);
              r = _out1649;
              resultingOwnership = _out1650;
            }
            readIdents = _3771_recIdents;
            return ;
          }
        } else if (_source154.is_Apply) {
          DAST._IExpression _3773___mcc_h212 = _source154.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _3774___mcc_h213 = _source154.dtor_args;
          bool _3775_isDatatype = _3421___mcc_h51;
          bool _3776_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3777_field = _3419___mcc_h49;
          DAST._IExpression _3778_on = _3418___mcc_h48;
          {
            RAST._IExpr _3779_onExpr;
            DCOMP._IOwnership _3780_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3781_recIdents;
            RAST._IExpr _out1651;
            DCOMP._IOwnership _out1652;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1653;
            (this).GenExpr(_3778_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1651, out _out1652, out _out1653);
            _3779_onExpr = _out1651;
            _3780_onOwned = _out1652;
            _3781_recIdents = _out1653;
            if ((_3775_isDatatype) || (_3776_isConstant)) {
              r = RAST.Expr.create_Call((_3779_onExpr).Sel(DCOMP.__default.escapeIdent(_3777_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1654;
              DCOMP._IOwnership _out1655;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1654, out _out1655);
              r = _out1654;
              resultingOwnership = _out1655;
            } else {
              Dafny.ISequence<Dafny.Rune> _3782_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3782_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3779_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3777_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1656;
              DCOMP._IOwnership _out1657;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3782_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1656, out _out1657);
              r = _out1656;
              resultingOwnership = _out1657;
            }
            readIdents = _3781_recIdents;
            return ;
          }
        } else if (_source154.is_TypeTest) {
          DAST._IExpression _3783___mcc_h216 = _source154.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3784___mcc_h217 = _source154.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _3785___mcc_h218 = _source154.dtor_variant;
          bool _3786_isDatatype = _3421___mcc_h51;
          bool _3787_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3788_field = _3419___mcc_h49;
          DAST._IExpression _3789_on = _3418___mcc_h48;
          {
            RAST._IExpr _3790_onExpr;
            DCOMP._IOwnership _3791_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3792_recIdents;
            RAST._IExpr _out1658;
            DCOMP._IOwnership _out1659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1660;
            (this).GenExpr(_3789_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1658, out _out1659, out _out1660);
            _3790_onExpr = _out1658;
            _3791_onOwned = _out1659;
            _3792_recIdents = _out1660;
            if ((_3786_isDatatype) || (_3787_isConstant)) {
              r = RAST.Expr.create_Call((_3790_onExpr).Sel(DCOMP.__default.escapeIdent(_3788_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1661;
              DCOMP._IOwnership _out1662;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1661, out _out1662);
              r = _out1661;
              resultingOwnership = _out1662;
            } else {
              Dafny.ISequence<Dafny.Rune> _3793_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3793_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3790_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3788_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1663;
              DCOMP._IOwnership _out1664;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3793_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1663, out _out1664);
              r = _out1663;
              resultingOwnership = _out1664;
            }
            readIdents = _3792_recIdents;
            return ;
          }
        } else if (_source154.is_InitializationValue) {
          DAST._IType _3794___mcc_h222 = _source154.dtor_typ;
          bool _3795_isDatatype = _3421___mcc_h51;
          bool _3796_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3797_field = _3419___mcc_h49;
          DAST._IExpression _3798_on = _3418___mcc_h48;
          {
            RAST._IExpr _3799_onExpr;
            DCOMP._IOwnership _3800_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3801_recIdents;
            RAST._IExpr _out1665;
            DCOMP._IOwnership _out1666;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1667;
            (this).GenExpr(_3798_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1665, out _out1666, out _out1667);
            _3799_onExpr = _out1665;
            _3800_onOwned = _out1666;
            _3801_recIdents = _out1667;
            if ((_3795_isDatatype) || (_3796_isConstant)) {
              r = RAST.Expr.create_Call((_3799_onExpr).Sel(DCOMP.__default.escapeIdent(_3797_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1668;
              DCOMP._IOwnership _out1669;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1668, out _out1669);
              r = _out1668;
              resultingOwnership = _out1669;
            } else {
              Dafny.ISequence<Dafny.Rune> _3802_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3802_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3799_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3797_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1670;
              DCOMP._IOwnership _out1671;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3802_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1670, out _out1671);
              r = _out1670;
              resultingOwnership = _out1671;
            }
            readIdents = _3801_recIdents;
            return ;
          }
        } else if (_source154.is_BoolBoundedPool) {
          bool _3803_isDatatype = _3421___mcc_h51;
          bool _3804_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3805_field = _3419___mcc_h49;
          DAST._IExpression _3806_on = _3418___mcc_h48;
          {
            RAST._IExpr _3807_onExpr;
            DCOMP._IOwnership _3808_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3809_recIdents;
            RAST._IExpr _out1672;
            DCOMP._IOwnership _out1673;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1674;
            (this).GenExpr(_3806_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1672, out _out1673, out _out1674);
            _3807_onExpr = _out1672;
            _3808_onOwned = _out1673;
            _3809_recIdents = _out1674;
            if ((_3803_isDatatype) || (_3804_isConstant)) {
              r = RAST.Expr.create_Call((_3807_onExpr).Sel(DCOMP.__default.escapeIdent(_3805_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1675;
              DCOMP._IOwnership _out1676;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1675, out _out1676);
              r = _out1675;
              resultingOwnership = _out1676;
            } else {
              Dafny.ISequence<Dafny.Rune> _3810_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3810_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3807_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3805_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1677;
              DCOMP._IOwnership _out1678;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3810_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1677, out _out1678);
              r = _out1677;
              resultingOwnership = _out1678;
            }
            readIdents = _3809_recIdents;
            return ;
          }
        } else if (_source154.is_SetBoundedPool) {
          DAST._IExpression _3811___mcc_h224 = _source154.dtor_of;
          bool _3812_isDatatype = _3421___mcc_h51;
          bool _3813_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3814_field = _3419___mcc_h49;
          DAST._IExpression _3815_on = _3418___mcc_h48;
          {
            RAST._IExpr _3816_onExpr;
            DCOMP._IOwnership _3817_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3818_recIdents;
            RAST._IExpr _out1679;
            DCOMP._IOwnership _out1680;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1681;
            (this).GenExpr(_3815_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1679, out _out1680, out _out1681);
            _3816_onExpr = _out1679;
            _3817_onOwned = _out1680;
            _3818_recIdents = _out1681;
            if ((_3812_isDatatype) || (_3813_isConstant)) {
              r = RAST.Expr.create_Call((_3816_onExpr).Sel(DCOMP.__default.escapeIdent(_3814_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1682;
              DCOMP._IOwnership _out1683;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1682, out _out1683);
              r = _out1682;
              resultingOwnership = _out1683;
            } else {
              Dafny.ISequence<Dafny.Rune> _3819_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3819_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3816_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3814_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1684;
              DCOMP._IOwnership _out1685;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3819_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1684, out _out1685);
              r = _out1684;
              resultingOwnership = _out1685;
            }
            readIdents = _3818_recIdents;
            return ;
          }
        } else if (_source154.is_SeqBoundedPool) {
          DAST._IExpression _3820___mcc_h226 = _source154.dtor_of;
          bool _3821___mcc_h227 = _source154.dtor_includeDuplicates;
          bool _3822_isDatatype = _3421___mcc_h51;
          bool _3823_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3824_field = _3419___mcc_h49;
          DAST._IExpression _3825_on = _3418___mcc_h48;
          {
            RAST._IExpr _3826_onExpr;
            DCOMP._IOwnership _3827_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3828_recIdents;
            RAST._IExpr _out1686;
            DCOMP._IOwnership _out1687;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1688;
            (this).GenExpr(_3825_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1686, out _out1687, out _out1688);
            _3826_onExpr = _out1686;
            _3827_onOwned = _out1687;
            _3828_recIdents = _out1688;
            if ((_3822_isDatatype) || (_3823_isConstant)) {
              r = RAST.Expr.create_Call((_3826_onExpr).Sel(DCOMP.__default.escapeIdent(_3824_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1689;
              DCOMP._IOwnership _out1690;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1689, out _out1690);
              r = _out1689;
              resultingOwnership = _out1690;
            } else {
              Dafny.ISequence<Dafny.Rune> _3829_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3829_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3826_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3824_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1691;
              DCOMP._IOwnership _out1692;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3829_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1691, out _out1692);
              r = _out1691;
              resultingOwnership = _out1692;
            }
            readIdents = _3828_recIdents;
            return ;
          }
        } else {
          DAST._IExpression _3830___mcc_h230 = _source154.dtor_lo;
          DAST._IExpression _3831___mcc_h231 = _source154.dtor_hi;
          bool _3832_isDatatype = _3421___mcc_h51;
          bool _3833_isConstant = _3420___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3834_field = _3419___mcc_h49;
          DAST._IExpression _3835_on = _3418___mcc_h48;
          {
            RAST._IExpr _3836_onExpr;
            DCOMP._IOwnership _3837_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3838_recIdents;
            RAST._IExpr _out1693;
            DCOMP._IOwnership _out1694;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1695;
            (this).GenExpr(_3835_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1693, out _out1694, out _out1695);
            _3836_onExpr = _out1693;
            _3837_onOwned = _out1694;
            _3838_recIdents = _out1695;
            if ((_3832_isDatatype) || (_3833_isConstant)) {
              r = RAST.Expr.create_Call((_3836_onExpr).Sel(DCOMP.__default.escapeIdent(_3834_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1696;
              DCOMP._IOwnership _out1697;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1696, out _out1697);
              r = _out1696;
              resultingOwnership = _out1697;
            } else {
              Dafny.ISequence<Dafny.Rune> _3839_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3839_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3836_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3834_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1698;
              DCOMP._IOwnership _out1699;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3839_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1698, out _out1699);
              r = _out1698;
              resultingOwnership = _out1699;
            }
            readIdents = _3838_recIdents;
            return ;
          }
        }
      } else if (_source151.is_SelectFn) {
        DAST._IExpression _3840___mcc_h234 = _source151.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _3841___mcc_h235 = _source151.dtor_field;
        bool _3842___mcc_h236 = _source151.dtor_onDatatype;
        bool _3843___mcc_h237 = _source151.dtor_isStatic;
        BigInteger _3844___mcc_h238 = _source151.dtor_arity;
        BigInteger _3845_arity = _3844___mcc_h238;
        bool _3846_isStatic = _3843___mcc_h237;
        bool _3847_isDatatype = _3842___mcc_h236;
        Dafny.ISequence<Dafny.Rune> _3848_field = _3841___mcc_h235;
        DAST._IExpression _3849_on = _3840___mcc_h234;
        {
          RAST._IExpr _3850_onExpr;
          DCOMP._IOwnership _3851_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3852_recIdents;
          RAST._IExpr _out1700;
          DCOMP._IOwnership _out1701;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1702;
          (this).GenExpr(_3849_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1700, out _out1701, out _out1702);
          _3850_onExpr = _out1700;
          _3851_onOwned = _out1701;
          _3852_recIdents = _out1702;
          Dafny.ISequence<Dafny.Rune> _3853_s = Dafny.Sequence<Dafny.Rune>.Empty;
          Dafny.ISequence<Dafny.Rune> _3854_onString;
          _3854_onString = (_3850_onExpr)._ToString(DCOMP.__default.IND);
          if (_3846_isStatic) {
            _3853_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3854_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_3848_field));
          } else {
            _3853_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            _3853_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3853_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _3854_onString), ((object.Equals(_3851_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _3855_args;
            _3855_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _3856_i;
            _3856_i = BigInteger.Zero;
            while ((_3856_i) < (_3845_arity)) {
              if ((_3856_i).Sign == 1) {
                _3855_args = Dafny.Sequence<Dafny.Rune>.Concat(_3855_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _3855_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3855_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_3856_i));
              _3856_i = (_3856_i) + (BigInteger.One);
            }
            _3853_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3853_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _3855_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            _3853_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3853_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _3848_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _3855_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            _3853_s = Dafny.Sequence<Dafny.Rune>.Concat(_3853_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _3853_s = Dafny.Sequence<Dafny.Rune>.Concat(_3853_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          Dafny.ISequence<Dafny.Rune> _3857_typeShape;
          _3857_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
          BigInteger _3858_i;
          _3858_i = BigInteger.Zero;
          while ((_3858_i) < (_3845_arity)) {
            if ((_3858_i).Sign == 1) {
              _3857_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_3857_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            _3857_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_3857_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
            _3858_i = (_3858_i) + (BigInteger.One);
          }
          _3857_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_3857_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
          _3853_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper(::std::rc::Rc::new("), _3853_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _3857_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">)"));
          r = RAST.Expr.create_RawExpr(_3853_s);
          RAST._IExpr _out1703;
          DCOMP._IOwnership _out1704;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1703, out _out1704);
          r = _out1703;
          resultingOwnership = _out1704;
          readIdents = _3852_recIdents;
          return ;
        }
      } else if (_source151.is_Index) {
        DAST._IExpression _3859___mcc_h239 = _source151.dtor_expr;
        DAST._ICollKind _3860___mcc_h240 = _source151.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _3861___mcc_h241 = _source151.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _3862_indices = _3861___mcc_h241;
        DAST._ICollKind _3863_collKind = _3860___mcc_h240;
        DAST._IExpression _3864_on = _3859___mcc_h239;
        {
          RAST._IExpr _3865_onExpr;
          DCOMP._IOwnership _3866_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3867_recIdents;
          RAST._IExpr _out1705;
          DCOMP._IOwnership _out1706;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1707;
          (this).GenExpr(_3864_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1705, out _out1706, out _out1707);
          _3865_onExpr = _out1705;
          _3866_onOwned = _out1706;
          _3867_recIdents = _out1707;
          readIdents = _3867_recIdents;
          r = _3865_onExpr;
          BigInteger _3868_i;
          _3868_i = BigInteger.Zero;
          while ((_3868_i) < (new BigInteger((_3862_indices).Count))) {
            if (object.Equals(_3863_collKind, DAST.CollKind.create_Array())) {
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IExpr _3869_idx;
            DCOMP._IOwnership _3870_idxOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3871_recIdentsIdx;
            RAST._IExpr _out1708;
            DCOMP._IOwnership _out1709;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1710;
            (this).GenExpr((_3862_indices).Select(_3868_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1708, out _out1709, out _out1710);
            _3869_idx = _out1708;
            _3870_idxOwned = _out1709;
            _3871_recIdentsIdx = _out1710;
            r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_3869_idx);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3871_recIdentsIdx);
            _3868_i = (_3868_i) + (BigInteger.One);
          }
          RAST._IExpr _out1711;
          DCOMP._IOwnership _out1712;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1711, out _out1712);
          r = _out1711;
          resultingOwnership = _out1712;
          return ;
        }
      } else if (_source151.is_IndexRange) {
        DAST._IExpression _3872___mcc_h242 = _source151.dtor_expr;
        bool _3873___mcc_h243 = _source151.dtor_isArray;
        Std.Wrappers._IOption<DAST._IExpression> _3874___mcc_h244 = _source151.dtor_low;
        Std.Wrappers._IOption<DAST._IExpression> _3875___mcc_h245 = _source151.dtor_high;
        Std.Wrappers._IOption<DAST._IExpression> _3876_high = _3875___mcc_h245;
        Std.Wrappers._IOption<DAST._IExpression> _3877_low = _3874___mcc_h244;
        bool _3878_isArray = _3873___mcc_h243;
        DAST._IExpression _3879_on = _3872___mcc_h242;
        {
          RAST._IExpr _3880_onExpr;
          DCOMP._IOwnership _3881_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3882_recIdents;
          RAST._IExpr _out1713;
          DCOMP._IOwnership _out1714;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1715;
          (this).GenExpr(_3879_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1713, out _out1714, out _out1715);
          _3880_onExpr = _out1713;
          _3881_onOwned = _out1714;
          _3882_recIdents = _out1715;
          readIdents = _3882_recIdents;
          Dafny.ISequence<Dafny.Rune> _3883_methodName;
          _3883_methodName = (((_3877_low).is_Some) ? ((((_3876_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_3876_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
          Dafny.ISequence<RAST._IExpr> _3884_arguments;
          _3884_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          Std.Wrappers._IOption<DAST._IExpression> _source155 = _3877_low;
          if (_source155.is_None) {
          } else {
            DAST._IExpression _3885___mcc_h274 = _source155.dtor_value;
            DAST._IExpression _3886_l = _3885___mcc_h274;
            {
              RAST._IExpr _3887_lExpr;
              DCOMP._IOwnership _3888___v118;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3889_recIdentsL;
              RAST._IExpr _out1716;
              DCOMP._IOwnership _out1717;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1718;
              (this).GenExpr(_3886_l, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1716, out _out1717, out _out1718);
              _3887_lExpr = _out1716;
              _3888___v118 = _out1717;
              _3889_recIdentsL = _out1718;
              _3884_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3884_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_3887_lExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3889_recIdentsL);
            }
          }
          Std.Wrappers._IOption<DAST._IExpression> _source156 = _3876_high;
          if (_source156.is_None) {
          } else {
            DAST._IExpression _3890___mcc_h275 = _source156.dtor_value;
            DAST._IExpression _3891_h = _3890___mcc_h275;
            {
              RAST._IExpr _3892_hExpr;
              DCOMP._IOwnership _3893___v119;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3894_recIdentsH;
              RAST._IExpr _out1719;
              DCOMP._IOwnership _out1720;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1721;
              (this).GenExpr(_3891_h, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1719, out _out1720, out _out1721);
              _3892_hExpr = _out1719;
              _3893___v119 = _out1720;
              _3894_recIdentsH = _out1721;
              _3884_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3884_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_3892_hExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3894_recIdentsH);
            }
          }
          r = _3880_onExpr;
          if (_3878_isArray) {
            if (!(_3883_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              _3883_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _3883_methodName);
            }
            r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _3883_methodName))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3884_arguments);
          } else {
            if (!(_3883_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              r = ((r).Sel(_3883_methodName)).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3884_arguments);
            }
          }
          RAST._IExpr _out1722;
          DCOMP._IOwnership _out1723;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1722, out _out1723);
          r = _out1722;
          resultingOwnership = _out1723;
          return ;
        }
      } else if (_source151.is_TupleSelect) {
        DAST._IExpression _3895___mcc_h246 = _source151.dtor_expr;
        BigInteger _3896___mcc_h247 = _source151.dtor_index;
        BigInteger _3897_idx = _3896___mcc_h247;
        DAST._IExpression _3898_on = _3895___mcc_h246;
        {
          RAST._IExpr _3899_onExpr;
          DCOMP._IOwnership _3900_onOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3901_recIdents;
          RAST._IExpr _out1724;
          DCOMP._IOwnership _out1725;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1726;
          (this).GenExpr(_3898_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1724, out _out1725, out _out1726);
          _3899_onExpr = _out1724;
          _3900_onOwnership = _out1725;
          _3901_recIdents = _out1726;
          r = (_3899_onExpr).Sel(Std.Strings.__default.OfNat(_3897_idx));
          RAST._IExpr _out1727;
          DCOMP._IOwnership _out1728;
          DCOMP.COMP.FromOwnership(r, _3900_onOwnership, expectedOwnership, out _out1727, out _out1728);
          r = _out1727;
          resultingOwnership = _out1728;
          readIdents = _3901_recIdents;
          return ;
        }
      } else if (_source151.is_Call) {
        DAST._IExpression _3902___mcc_h248 = _source151.dtor_on;
        DAST._ICallName _3903___mcc_h249 = _source151.dtor_callName;
        Dafny.ISequence<DAST._IType> _3904___mcc_h250 = _source151.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _3905___mcc_h251 = _source151.dtor_args;
        Dafny.ISequence<DAST._IExpression> _3906_args = _3905___mcc_h251;
        Dafny.ISequence<DAST._IType> _3907_typeArgs = _3904___mcc_h250;
        DAST._ICallName _3908_name = _3903___mcc_h249;
        DAST._IExpression _3909_on = _3902___mcc_h248;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IType> _3910_typeExprs;
          _3910_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_3907_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _3911_typeI;
            _3911_typeI = BigInteger.Zero;
            while ((_3911_typeI) < (new BigInteger((_3907_typeArgs).Count))) {
              RAST._IType _3912_typeExpr;
              RAST._IType _out1729;
              _out1729 = (this).GenType((_3907_typeArgs).Select(_3911_typeI), false, false);
              _3912_typeExpr = _out1729;
              _3910_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_3910_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_3912_typeExpr));
              _3911_typeI = (_3911_typeI) + (BigInteger.One);
            }
          }
          Dafny.ISequence<RAST._IExpr> _3913_argExprs;
          _3913_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _3914_i;
          _3914_i = BigInteger.Zero;
          while ((_3914_i) < (new BigInteger((_3906_args).Count))) {
            RAST._IExpr _3915_argExpr;
            DCOMP._IOwnership _3916_argOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3917_argIdents;
            RAST._IExpr _out1730;
            DCOMP._IOwnership _out1731;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1732;
            (this).GenExpr((_3906_args).Select(_3914_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1730, out _out1731, out _out1732);
            _3915_argExpr = _out1730;
            _3916_argOwnership = _out1731;
            _3917_argIdents = _out1732;
            _3913_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_3913_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_3915_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3917_argIdents);
            _3914_i = (_3914_i) + (BigInteger.One);
          }
          RAST._IExpr _3918_onExpr;
          DCOMP._IOwnership _3919___v120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3920_recIdents;
          RAST._IExpr _out1733;
          DCOMP._IOwnership _out1734;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1735;
          (this).GenExpr(_3909_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1733, out _out1734, out _out1735);
          _3918_onExpr = _out1733;
          _3919___v120 = _out1734;
          _3920_recIdents = _out1735;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3920_recIdents);
          Dafny.ISequence<Dafny.Rune> _3921_renderedName;
          _3921_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source157) => {
            if (_source157.is_Name) {
              Dafny.ISequence<Dafny.Rune> _3922___mcc_h276 = _source157.dtor_name;
              Dafny.ISequence<Dafny.Rune> _3923_ident = _3922___mcc_h276;
              return DCOMP.__default.escapeIdent(_3923_ident);
            } else if (_source157.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source157.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source157.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_3908_name);
          DAST._IExpression _source158 = _3909_on;
          if (_source158.is_Literal) {
            DAST._ILiteral _3924___mcc_h277 = _source158.dtor_Literal_a0;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _3925___mcc_h279 = _source158.dtor_Ident_a0;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3926___mcc_h281 = _source158.dtor_Companion_a0;
            {
              _3918_onExpr = (_3918_onExpr).MSel(_3921_renderedName);
            }
          } else if (_source158.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _3927___mcc_h283 = _source158.dtor_Tuple_a0;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3928___mcc_h285 = _source158.dtor_path;
            Dafny.ISequence<DAST._IType> _3929___mcc_h286 = _source158.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _3930___mcc_h287 = _source158.dtor_args;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _3931___mcc_h291 = _source158.dtor_dims;
            DAST._IType _3932___mcc_h292 = _source158.dtor_typ;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3933___mcc_h295 = _source158.dtor_path;
            Dafny.ISequence<DAST._IType> _3934___mcc_h296 = _source158.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _3935___mcc_h297 = _source158.dtor_variant;
            bool _3936___mcc_h298 = _source158.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3937___mcc_h299 = _source158.dtor_contents;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_Convert) {
            DAST._IExpression _3938___mcc_h305 = _source158.dtor_value;
            DAST._IType _3939___mcc_h306 = _source158.dtor_from;
            DAST._IType _3940___mcc_h307 = _source158.dtor_typ;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_SeqConstruct) {
            DAST._IExpression _3941___mcc_h311 = _source158.dtor_length;
            DAST._IExpression _3942___mcc_h312 = _source158.dtor_elem;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _3943___mcc_h315 = _source158.dtor_elements;
            DAST._IType _3944___mcc_h316 = _source158.dtor_typ;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _3945___mcc_h319 = _source158.dtor_elements;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _3946___mcc_h321 = _source158.dtor_elements;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3947___mcc_h323 = _source158.dtor_mapElems;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_MapBuilder) {
            DAST._IType _3948___mcc_h325 = _source158.dtor_keyType;
            DAST._IType _3949___mcc_h326 = _source158.dtor_valueType;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_SeqUpdate) {
            DAST._IExpression _3950___mcc_h329 = _source158.dtor_expr;
            DAST._IExpression _3951___mcc_h330 = _source158.dtor_indexExpr;
            DAST._IExpression _3952___mcc_h331 = _source158.dtor_value;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_MapUpdate) {
            DAST._IExpression _3953___mcc_h335 = _source158.dtor_expr;
            DAST._IExpression _3954___mcc_h336 = _source158.dtor_indexExpr;
            DAST._IExpression _3955___mcc_h337 = _source158.dtor_value;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_SetBuilder) {
            DAST._IType _3956___mcc_h341 = _source158.dtor_elemType;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_ToMultiset) {
            DAST._IExpression _3957___mcc_h343 = _source158.dtor_ToMultiset_a0;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_This) {
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_Ite) {
            DAST._IExpression _3958___mcc_h345 = _source158.dtor_cond;
            DAST._IExpression _3959___mcc_h346 = _source158.dtor_thn;
            DAST._IExpression _3960___mcc_h347 = _source158.dtor_els;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_UnOp) {
            DAST._IUnaryOp _3961___mcc_h351 = _source158.dtor_unOp;
            DAST._IExpression _3962___mcc_h352 = _source158.dtor_expr;
            DAST.Format._IUnaryOpFormat _3963___mcc_h353 = _source158.dtor_format1;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_BinOp) {
            DAST._IBinOp _3964___mcc_h357 = _source158.dtor_op;
            DAST._IExpression _3965___mcc_h358 = _source158.dtor_left;
            DAST._IExpression _3966___mcc_h359 = _source158.dtor_right;
            DAST.Format._IBinaryOpFormat _3967___mcc_h360 = _source158.dtor_format2;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_ArrayLen) {
            DAST._IExpression _3968___mcc_h365 = _source158.dtor_expr;
            BigInteger _3969___mcc_h366 = _source158.dtor_dim;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_MapKeys) {
            DAST._IExpression _3970___mcc_h369 = _source158.dtor_expr;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_MapValues) {
            DAST._IExpression _3971___mcc_h371 = _source158.dtor_expr;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_Select) {
            DAST._IExpression _3972___mcc_h373 = _source158.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _3973___mcc_h374 = _source158.dtor_field;
            bool _3974___mcc_h375 = _source158.dtor_isConstant;
            bool _3975___mcc_h376 = _source158.dtor_onDatatype;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_SelectFn) {
            DAST._IExpression _3976___mcc_h381 = _source158.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _3977___mcc_h382 = _source158.dtor_field;
            bool _3978___mcc_h383 = _source158.dtor_onDatatype;
            bool _3979___mcc_h384 = _source158.dtor_isStatic;
            BigInteger _3980___mcc_h385 = _source158.dtor_arity;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_Index) {
            DAST._IExpression _3981___mcc_h391 = _source158.dtor_expr;
            DAST._ICollKind _3982___mcc_h392 = _source158.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _3983___mcc_h393 = _source158.dtor_indices;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_IndexRange) {
            DAST._IExpression _3984___mcc_h397 = _source158.dtor_expr;
            bool _3985___mcc_h398 = _source158.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _3986___mcc_h399 = _source158.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _3987___mcc_h400 = _source158.dtor_high;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_TupleSelect) {
            DAST._IExpression _3988___mcc_h405 = _source158.dtor_expr;
            BigInteger _3989___mcc_h406 = _source158.dtor_index;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_Call) {
            DAST._IExpression _3990___mcc_h409 = _source158.dtor_on;
            DAST._ICallName _3991___mcc_h410 = _source158.dtor_callName;
            Dafny.ISequence<DAST._IType> _3992___mcc_h411 = _source158.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _3993___mcc_h412 = _source158.dtor_args;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _3994___mcc_h417 = _source158.dtor_params;
            DAST._IType _3995___mcc_h418 = _source158.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _3996___mcc_h419 = _source158.dtor_body;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _3997___mcc_h423 = _source158.dtor_values;
            DAST._IType _3998___mcc_h424 = _source158.dtor_retType;
            DAST._IExpression _3999___mcc_h425 = _source158.dtor_expr;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _4000___mcc_h429 = _source158.dtor_name;
            DAST._IType _4001___mcc_h430 = _source158.dtor_typ;
            DAST._IExpression _4002___mcc_h431 = _source158.dtor_value;
            DAST._IExpression _4003___mcc_h432 = _source158.dtor_iifeBody;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_Apply) {
            DAST._IExpression _4004___mcc_h437 = _source158.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _4005___mcc_h438 = _source158.dtor_args;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_TypeTest) {
            DAST._IExpression _4006___mcc_h441 = _source158.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4007___mcc_h442 = _source158.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _4008___mcc_h443 = _source158.dtor_variant;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_InitializationValue) {
            DAST._IType _4009___mcc_h447 = _source158.dtor_typ;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_BoolBoundedPool) {
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_SetBoundedPool) {
            DAST._IExpression _4010___mcc_h449 = _source158.dtor_of;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else if (_source158.is_SeqBoundedPool) {
            DAST._IExpression _4011___mcc_h451 = _source158.dtor_of;
            bool _4012___mcc_h452 = _source158.dtor_includeDuplicates;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          } else {
            DAST._IExpression _4013___mcc_h455 = _source158.dtor_lo;
            DAST._IExpression _4014___mcc_h456 = _source158.dtor_hi;
            {
              _3918_onExpr = (_3918_onExpr).Sel(_3921_renderedName);
            }
          }
          r = RAST.Expr.create_Call(_3918_onExpr, _3910_typeExprs, _3913_argExprs);
          RAST._IExpr _out1736;
          DCOMP._IOwnership _out1737;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1736, out _out1737);
          r = _out1736;
          resultingOwnership = _out1737;
          return ;
        }
      } else if (_source151.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _4015___mcc_h252 = _source151.dtor_params;
        DAST._IType _4016___mcc_h253 = _source151.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _4017___mcc_h254 = _source151.dtor_body;
        Dafny.ISequence<DAST._IStatement> _4018_body = _4017___mcc_h254;
        DAST._IType _4019_retType = _4016___mcc_h253;
        Dafny.ISequence<DAST._IFormal> _4020_params = _4015___mcc_h252;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4021_paramNames;
          _4021_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4022_i;
          _4022_i = BigInteger.Zero;
          while ((_4022_i) < (new BigInteger((_4020_params).Count))) {
            _4021_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_4021_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_4020_params).Select(_4022_i)).dtor_name));
            _4022_i = (_4022_i) + (BigInteger.One);
          }
          RAST._IExpr _4023_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4024_recIdents;
          RAST._IExpr _out1738;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1739;
          (this).GenStmts(_4018_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _4021_paramNames, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out1738, out _out1739);
          _4023_recursiveGen = _out1738;
          _4024_recIdents = _out1739;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _4025_allReadCloned;
          _4025_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_4024_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _4026_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_4024_recIdents).Elements) {
              _4026_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
              if ((_4024_recIdents).Contains(_4026_next)) {
                goto after__ASSIGN_SUCH_THAT_3;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 3286)");
          after__ASSIGN_SUCH_THAT_3: ;
            if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_4026_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
              if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                _4025_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(_4025_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let _this = self.clone();\n"));
              }
            } else if (!((_4021_paramNames).Contains(_4026_next))) {
              _4025_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4025_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent(_4026_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), DCOMP.__default.escapeIdent(_4026_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4026_next));
            }
            _4024_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4024_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4026_next));
          }
          Dafny.ISequence<Dafny.Rune> _4027_paramsString;
          _4027_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          Dafny.ISequence<Dafny.Rune> _4028_paramTypes;
          _4028_paramTypes = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _4022_i = BigInteger.Zero;
          while ((_4022_i) < (new BigInteger((_4020_params).Count))) {
            if ((_4022_i).Sign == 1) {
              _4027_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_4027_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              _4028_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_4028_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IType _4029_typStr;
            RAST._IType _out1740;
            _out1740 = (this).GenType(((_4020_params).Select(_4022_i)).dtor_typ, false, true);
            _4029_typStr = _out1740;
            _4027_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4027_paramsString, DCOMP.__default.escapeIdent(((_4020_params).Select(_4022_i)).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (RAST.Type.create_Borrowed(_4029_typStr))._ToString(DCOMP.__default.IND));
            _4028_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_4028_paramTypes, (RAST.Type.create_Borrowed(_4029_typStr))._ToString(DCOMP.__default.IND));
            _4022_i = (_4022_i) + (BigInteger.One);
          }
          RAST._IType _4030_retTypeGen;
          RAST._IType _out1741;
          _out1741 = (this).GenType(_4019_retType, false, true);
          _4030_retTypeGen = _out1741;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn("), _4028_paramTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), (_4030_retTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>({\n")), _4025_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(move |")), _4027_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), (_4030_retTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), (_4023_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})")));
          RAST._IExpr _out1742;
          DCOMP._IOwnership _out1743;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1742, out _out1743);
          r = _out1742;
          resultingOwnership = _out1743;
          return ;
        }
      } else if (_source151.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4031___mcc_h255 = _source151.dtor_values;
        DAST._IType _4032___mcc_h256 = _source151.dtor_retType;
        DAST._IExpression _4033___mcc_h257 = _source151.dtor_expr;
        DAST._IExpression _4034_expr = _4033___mcc_h257;
        DAST._IType _4035_retType = _4032___mcc_h256;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4036_values = _4031___mcc_h255;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4037_paramNames;
          _4037_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4038_paramNamesSet;
          _4038_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4039_i;
          _4039_i = BigInteger.Zero;
          while ((_4039_i) < (new BigInteger((_4036_values).Count))) {
            _4037_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_4037_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((_4036_values).Select(_4039_i)).dtor__0).dtor_name));
            _4038_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4038_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((((_4036_values).Select(_4039_i)).dtor__0).dtor_name));
            _4039_i = (_4039_i) + (BigInteger.One);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _4040_s;
          _4040_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          Dafny.ISequence<Dafny.Rune> _4041_paramsString;
          _4041_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _4039_i = BigInteger.Zero;
          while ((_4039_i) < (new BigInteger((_4036_values).Count))) {
            if ((_4039_i).Sign == 1) {
              _4041_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_4041_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IType _4042_typStr;
            RAST._IType _out1744;
            _out1744 = (this).GenType((((_4036_values).Select(_4039_i)).dtor__0).dtor_typ, false, true);
            _4042_typStr = _out1744;
            RAST._IExpr _4043_valueGen;
            DCOMP._IOwnership _4044___v123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4045_recIdents;
            RAST._IExpr _out1745;
            DCOMP._IOwnership _out1746;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1747;
            (this).GenExpr(((_4036_values).Select(_4039_i)).dtor__1, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1745, out _out1746, out _out1747);
            _4043_valueGen = _out1745;
            _4044___v123 = _out1746;
            _4045_recIdents = _out1747;
            _4040_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4040_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent((((_4036_values).Select(_4039_i)).dtor__0).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_4042_typStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4045_recIdents);
            _4040_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4040_s, (_4043_valueGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            _4039_i = (_4039_i) + (BigInteger.One);
          }
          RAST._IExpr _4046_recGen;
          DCOMP._IOwnership _4047_recOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4048_recIdents;
          RAST._IExpr _out1748;
          DCOMP._IOwnership _out1749;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1750;
          (this).GenExpr(_4034_expr, selfIdent, _4037_paramNames, expectedOwnership, out _out1748, out _out1749, out _out1750);
          _4046_recGen = _out1748;
          _4047_recOwned = _out1749;
          _4048_recIdents = _out1750;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4048_recIdents, _4038_paramNamesSet);
          _4040_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4040_s, (_4046_recGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          r = RAST.Expr.create_RawExpr(_4040_s);
          RAST._IExpr _out1751;
          DCOMP._IOwnership _out1752;
          DCOMP.COMP.FromOwnership(r, _4047_recOwned, expectedOwnership, out _out1751, out _out1752);
          r = _out1751;
          resultingOwnership = _out1752;
          return ;
        }
      } else if (_source151.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _4049___mcc_h258 = _source151.dtor_name;
        DAST._IType _4050___mcc_h259 = _source151.dtor_typ;
        DAST._IExpression _4051___mcc_h260 = _source151.dtor_value;
        DAST._IExpression _4052___mcc_h261 = _source151.dtor_iifeBody;
        DAST._IExpression _4053_iifeBody = _4052___mcc_h261;
        DAST._IExpression _4054_value = _4051___mcc_h260;
        DAST._IType _4055_tpe = _4050___mcc_h259;
        Dafny.ISequence<Dafny.Rune> _4056_name = _4049___mcc_h258;
        {
          RAST._IExpr _4057_valueGen;
          DCOMP._IOwnership _4058___v124;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4059_recIdents;
          RAST._IExpr _out1753;
          DCOMP._IOwnership _out1754;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1755;
          (this).GenExpr(_4054_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1753, out _out1754, out _out1755);
          _4057_valueGen = _out1753;
          _4058___v124 = _out1754;
          _4059_recIdents = _out1755;
          readIdents = _4059_recIdents;
          RAST._IType _4060_valueTypeGen;
          RAST._IType _out1756;
          _out1756 = (this).GenType(_4055_tpe, false, true);
          _4060_valueTypeGen = _out1756;
          RAST._IExpr _4061_bodyGen;
          DCOMP._IOwnership _4062___v125;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4063_bodyIdents;
          RAST._IExpr _out1757;
          DCOMP._IOwnership _out1758;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1759;
          (this).GenExpr(_4053_iifeBody, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1757, out _out1758, out _out1759);
          _4061_bodyGen = _out1757;
          _4062___v125 = _out1758;
          _4063_bodyIdents = _out1759;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4063_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_4056_name))));
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet "), DCOMP.__default.escapeIdent((_4056_name))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_4060_valueTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (_4057_valueGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), (_4061_bodyGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")));
          RAST._IExpr _out1760;
          DCOMP._IOwnership _out1761;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1760, out _out1761);
          r = _out1760;
          resultingOwnership = _out1761;
          return ;
        }
      } else if (_source151.is_Apply) {
        DAST._IExpression _4064___mcc_h262 = _source151.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _4065___mcc_h263 = _source151.dtor_args;
        Dafny.ISequence<DAST._IExpression> _4066_args = _4065___mcc_h263;
        DAST._IExpression _4067_func = _4064___mcc_h262;
        {
          RAST._IExpr _4068_funcExpr;
          DCOMP._IOwnership _4069___v126;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4070_recIdents;
          RAST._IExpr _out1762;
          DCOMP._IOwnership _out1763;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1764;
          (this).GenExpr(_4067_func, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1762, out _out1763, out _out1764);
          _4068_funcExpr = _out1762;
          _4069___v126 = _out1763;
          _4070_recIdents = _out1764;
          readIdents = _4070_recIdents;
          Dafny.ISequence<Dafny.Rune> _4071_argString;
          _4071_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _4072_i;
          _4072_i = BigInteger.Zero;
          while ((_4072_i) < (new BigInteger((_4066_args).Count))) {
            if ((_4072_i).Sign == 1) {
              _4071_argString = Dafny.Sequence<Dafny.Rune>.Concat(_4071_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IExpr _4073_argExpr;
            DCOMP._IOwnership _4074_argOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4075_argIdents;
            RAST._IExpr _out1765;
            DCOMP._IOwnership _out1766;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1767;
            (this).GenExpr((_4066_args).Select(_4072_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1765, out _out1766, out _out1767);
            _4073_argExpr = _out1765;
            _4074_argOwned = _out1766;
            _4075_argIdents = _out1767;
            Dafny.ISequence<Dafny.Rune> _4076_argExprString;
            _4076_argExprString = (_4073_argExpr)._ToString(DCOMP.__default.IND);
            if (object.Equals(_4074_argOwned, DCOMP.Ownership.create_OwnershipOwned())) {
              _4076_argExprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _4076_argExprString);
            }
            _4071_argString = Dafny.Sequence<Dafny.Rune>.Concat(_4071_argString, _4076_argExprString);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4075_argIdents);
            _4072_i = (_4072_i) + (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_4068_funcExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _4071_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))")));
          RAST._IExpr _out1768;
          DCOMP._IOwnership _out1769;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1768, out _out1769);
          r = _out1768;
          resultingOwnership = _out1769;
          return ;
        }
      } else if (_source151.is_TypeTest) {
        DAST._IExpression _4077___mcc_h264 = _source151.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4078___mcc_h265 = _source151.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _4079___mcc_h266 = _source151.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _4080_variant = _4079___mcc_h266;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4081_dType = _4078___mcc_h265;
        DAST._IExpression _4082_on = _4077___mcc_h264;
        {
          RAST._IExpr _4083_exprGen;
          DCOMP._IOwnership _4084___v127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4085_recIdents;
          RAST._IExpr _out1770;
          DCOMP._IOwnership _out1771;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1772;
          (this).GenExpr(_4082_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1770, out _out1771, out _out1772);
          _4083_exprGen = _out1770;
          _4084___v127 = _out1771;
          _4085_recIdents = _out1772;
          Dafny.ISequence<Dafny.Rune> _4086_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1773;
          _out1773 = DCOMP.COMP.GenPath(_4081_dType);
          _4086_dTypePath = _out1773;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), (_4083_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _4086_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_4080_variant)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })")));
          RAST._IExpr _out1774;
          DCOMP._IOwnership _out1775;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1774, out _out1775);
          r = _out1774;
          resultingOwnership = _out1775;
          readIdents = _4085_recIdents;
          return ;
        }
      } else if (_source151.is_InitializationValue) {
        DAST._IType _4087___mcc_h267 = _source151.dtor_typ;
        DAST._IType _4088_typ = _4087___mcc_h267;
        {
          RAST._IType _4089_typExpr;
          RAST._IType _out1776;
          _out1776 = (this).GenType(_4088_typ, false, false);
          _4089_typExpr = _out1776;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_4089_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
          RAST._IExpr _out1777;
          DCOMP._IOwnership _out1778;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1777, out _out1778);
          r = _out1777;
          resultingOwnership = _out1778;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source151.is_BoolBoundedPool) {
        {
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
          RAST._IExpr _out1779;
          DCOMP._IOwnership _out1780;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1779, out _out1780);
          r = _out1779;
          resultingOwnership = _out1780;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source151.is_SetBoundedPool) {
        DAST._IExpression _4090___mcc_h268 = _source151.dtor_of;
        DAST._IExpression _4091_of = _4090___mcc_h268;
        {
          RAST._IExpr _4092_exprGen;
          DCOMP._IOwnership _4093___v128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4094_recIdents;
          RAST._IExpr _out1781;
          DCOMP._IOwnership _out1782;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1783;
          (this).GenExpr(_4091_of, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1781, out _out1782, out _out1783);
          _4092_exprGen = _out1781;
          _4093___v128 = _out1782;
          _4094_recIdents = _out1783;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_4092_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").iter()")));
          RAST._IExpr _out1784;
          DCOMP._IOwnership _out1785;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1784, out _out1785);
          r = _out1784;
          resultingOwnership = _out1785;
          readIdents = _4094_recIdents;
          return ;
        }
      } else if (_source151.is_SeqBoundedPool) {
        DAST._IExpression _4095___mcc_h269 = _source151.dtor_of;
        bool _4096___mcc_h270 = _source151.dtor_includeDuplicates;
        bool _4097_includeDuplicates = _4096___mcc_h270;
        DAST._IExpression _4098_of = _4095___mcc_h269;
        {
          RAST._IExpr _4099_exprGen;
          DCOMP._IOwnership _4100___v129;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4101_recIdents;
          RAST._IExpr _out1786;
          DCOMP._IOwnership _out1787;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1788;
          (this).GenExpr(_4098_of, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1786, out _out1787, out _out1788);
          _4099_exprGen = _out1786;
          _4100___v129 = _out1787;
          _4101_recIdents = _out1788;
          Dafny.ISequence<Dafny.Rune> _4102_s;
          _4102_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_4099_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").iter()"));
          if (!(_4097_includeDuplicates)) {
            _4102_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::itertools::Itertools::unique("), _4102_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          r = RAST.Expr.create_RawExpr(_4102_s);
          RAST._IExpr _out1789;
          DCOMP._IOwnership _out1790;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1789, out _out1790);
          r = _out1789;
          resultingOwnership = _out1790;
          readIdents = _4101_recIdents;
          return ;
        }
      } else {
        DAST._IExpression _4103___mcc_h271 = _source151.dtor_lo;
        DAST._IExpression _4104___mcc_h272 = _source151.dtor_hi;
        DAST._IExpression _4105_hi = _4104___mcc_h272;
        DAST._IExpression _4106_lo = _4103___mcc_h271;
        {
          RAST._IExpr _4107_lo;
          DCOMP._IOwnership _4108___v130;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4109_recIdentsLo;
          RAST._IExpr _out1791;
          DCOMP._IOwnership _out1792;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1793;
          (this).GenExpr(_4106_lo, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1791, out _out1792, out _out1793);
          _4107_lo = _out1791;
          _4108___v130 = _out1792;
          _4109_recIdentsLo = _out1793;
          RAST._IExpr _4110_hi;
          DCOMP._IOwnership _4111___v131;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4112_recIdentsHi;
          RAST._IExpr _out1794;
          DCOMP._IOwnership _out1795;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1796;
          (this).GenExpr(_4105_hi, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1794, out _out1795, out _out1796);
          _4110_hi = _out1794;
          _4111___v131 = _out1795;
          _4112_recIdentsHi = _out1796;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::integer_range("), (_4107_lo)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), (_4110_hi)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          RAST._IExpr _out1797;
          DCOMP._IOwnership _out1798;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1797, out _out1798);
          r = _out1797;
          resultingOwnership = _out1798;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4109_recIdentsLo, _4112_recIdentsHi);
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern crate dafny_runtime;\n"));
      BigInteger _4113_i;
      _4113_i = BigInteger.Zero;
      while ((_4113_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _4114_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _4115_m;
        RAST._IMod _out1799;
        _out1799 = (this).GenModule((p).Select(_4113_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _4115_m = _out1799;
        _4114_generated = (_4115_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_4113_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _4114_generated);
        _4113_i = (_4113_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _4116_i;
      _4116_i = BigInteger.Zero;
      while ((_4116_i) < (new BigInteger((fullName).Count))) {
        if ((_4116_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeIdent((fullName).Select(_4116_i)));
        _4116_i = (_4116_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
    public bool _UnicodeChars {get; set;}
    public bool UnicodeChars { get {
      return this._UnicodeChars;
    } }
    public Dafny.ISequence<Dafny.Rune> DafnyChar { get {
      if ((this).UnicodeChars) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyChar");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyCharUTF16");
      }
    } }
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
  }
} // end of namespace DCOMP