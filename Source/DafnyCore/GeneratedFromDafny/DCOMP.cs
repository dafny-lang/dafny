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
      Dafny.ISequence<Dafny.Rune> _1855___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1855___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1855___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1855___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _1855___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1855___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1856___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1856___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1856___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1856___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _1856___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1856___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1857_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1857_r);
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
      Dafny.ISequence<RAST._IModDecl> _1858_body;
      Dafny.ISequence<RAST._IModDecl> _out15;
      _out15 = (this).GenModuleBody((mod).dtor_body, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
      _1858_body = _out15;
      s = (((mod).dtor_isExtern) ? (RAST.Mod.create_ExternMod(DCOMP.__default.escapeIdent((mod).dtor_name))) : (RAST.Mod.create_Mod(DCOMP.__default.escapeIdent((mod).dtor_name), _1858_body)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _1859_i;
      _1859_i = BigInteger.Zero;
      while ((_1859_i) < (new BigInteger((body).Count))) {
        Dafny.ISequence<RAST._IModDecl> _1860_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source55 = (body).Select(_1859_i);
        if (_source55.is_Module) {
          DAST._IModule _1861___mcc_h0 = _source55.dtor_Module_a0;
          DAST._IModule _1862_m = _1861___mcc_h0;
          RAST._IMod _1863_mm;
          RAST._IMod _out16;
          _out16 = (this).GenModule(_1862_m, containingPath);
          _1863_mm = _out16;
          _1860_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1863_mm));
        } else if (_source55.is_Class) {
          DAST._IClass _1864___mcc_h1 = _source55.dtor_Class_a0;
          DAST._IClass _1865_c = _1864___mcc_h1;
          Dafny.ISequence<RAST._IModDecl> _out17;
          _out17 = (this).GenClass(_1865_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1865_c).dtor_name)));
          _1860_generated = _out17;
        } else if (_source55.is_Trait) {
          DAST._ITrait _1866___mcc_h2 = _source55.dtor_Trait_a0;
          DAST._ITrait _1867_t = _1866___mcc_h2;
          Dafny.ISequence<Dafny.Rune> _1868_tt;
          Dafny.ISequence<Dafny.Rune> _out18;
          _out18 = (this).GenTrait(_1867_t, containingPath);
          _1868_tt = _out18;
          _1860_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1868_tt));
        } else if (_source55.is_Newtype) {
          DAST._INewtype _1869___mcc_h3 = _source55.dtor_Newtype_a0;
          DAST._INewtype _1870_n = _1869___mcc_h3;
          Dafny.ISequence<RAST._IModDecl> _out19;
          _out19 = (this).GenNewtype(_1870_n);
          _1860_generated = _out19;
        } else {
          DAST._IDatatype _1871___mcc_h4 = _source55.dtor_Datatype_a0;
          DAST._IDatatype _1872_d = _1871___mcc_h4;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenDatatype(_1872_d);
          _1860_generated = _out20;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1860_generated);
        _1859_i = (_1859_i) + (BigInteger.One);
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
      BigInteger _1873_tpI;
      _1873_tpI = BigInteger.Zero;
      if ((new BigInteger((@params).Count)).Sign == 1) {
        while ((_1873_tpI) < (new BigInteger((@params).Count))) {
          DAST._IType _1874_tp;
          _1874_tp = (@params).Select(_1873_tpI);
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1874_tp));
          RAST._IType _1875_genTp;
          RAST._IType _out21;
          _out21 = (this).GenType(_1874_tp, false, false);
          _1875_genTp = _out21;
          typeParams = Dafny.Sequence<RAST._ITypeParam>.Concat(typeParams, Dafny.Sequence<RAST._ITypeParam>.FromElements(RAST.TypeParam.create((_1875_genTp)._ToString(DCOMP.__default.IND), Dafny.Sequence<RAST._IType>.FromElements())));
          _1873_tpI = (_1873_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<RAST._IType> _1876_baseConstraints;
      _1876_baseConstraints = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.CloneTrait, RAST.__default.DafnyPrintTrait, RAST.__default.StaticTrait);
      constrainedTypeParams = RAST.TypeParam.AddConstraintsMultiple(typeParams, _1876_baseConstraints);
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1877_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1878_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1879_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1880_whereConstraints;
      Dafny.ISet<DAST._IType> _out22;
      Dafny.ISequence<RAST._ITypeParam> _out23;
      Dafny.ISequence<RAST._ITypeParam> _out24;
      Dafny.ISequence<Dafny.Rune> _out25;
      (this).GenTypeParameters((c).dtor_typeParams, out _out22, out _out23, out _out24, out _out25);
      _1877_typeParamsSet = _out22;
      _1878_sTypeParams = _out23;
      _1879_sConstrainedTypeParams = _out24;
      _1880_whereConstraints = _out25;
      Dafny.ISequence<Dafny.Rune> _1881_constrainedTypeParams;
      _1881_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1879_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IFormal> _1882_fields;
      _1882_fields = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1883_fieldInits;
      _1883_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _1884_fieldI;
      _1884_fieldI = BigInteger.Zero;
      while ((_1884_fieldI) < (new BigInteger(((c).dtor_fields).Count))) {
        DAST._IField _1885_field;
        _1885_field = ((c).dtor_fields).Select(_1884_fieldI);
        RAST._IType _1886_fieldType;
        RAST._IType _out26;
        _out26 = (this).GenType(((_1885_field).dtor_formal).dtor_typ, false, false);
        _1886_fieldType = _out26;
        _1882_fields = Dafny.Sequence<RAST._IFormal>.Concat(_1882_fields, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub "), DCOMP.__default.escapeIdent(((_1885_field).dtor_formal).dtor_name)), RAST.Type.create_TypeApp(RAST.__default.refcell__type, Dafny.Sequence<RAST._IType>.FromElements(_1886_fieldType)))));
        Std.Wrappers._IOption<DAST._IExpression> _source56 = (_1885_field).dtor_defaultValue;
        if (_source56.is_None) {
          {
            _1883_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1883_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(((_1885_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new(::std::default::Default::default())")))));
          }
        } else {
          DAST._IExpression _1887___mcc_h0 = _source56.dtor_value;
          DAST._IExpression _1888_e = _1887___mcc_h0;
          {
            RAST._IExpr _1889_eStr;
            DCOMP._IOwnership _1890___v30;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1891___v31;
            RAST._IExpr _out27;
            DCOMP._IOwnership _out28;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out29;
            (this).GenExpr(_1888_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out27, out _out28, out _out29);
            _1889_eStr = _out27;
            _1890___v30 = _out28;
            _1891___v31 = _out29;
            _1883_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1883_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(((_1885_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1889_eStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
          }
        }
        _1884_fieldI = (_1884_fieldI) + (BigInteger.One);
      }
      BigInteger _1892_typeParamI;
      _1892_typeParamI = BigInteger.Zero;
      while ((_1892_typeParamI) < (new BigInteger(((c).dtor_typeParams).Count))) {
        RAST._IType _1893_tpeGen;
        RAST._IType _out30;
        _out30 = (this).GenType(((c).dtor_typeParams).Select(_1892_typeParamI), false, false);
        _1893_tpeGen = _out30;
        _1882_fields = Dafny.Sequence<RAST._IFormal>.Concat(_1882_fields, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1892_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1893_tpeGen)))));
        _1883_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1883_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1892_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
        _1892_typeParamI = (_1892_typeParamI) + (BigInteger.One);
      }
      RAST._IStruct _1894_struct;
      _1894_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.__default.escapeIdent((c).dtor_name), _1878_sTypeParams, RAST.Formals.create_NamedFormals(_1882_fields));
      Dafny.ISequence<RAST._IType> _1895_typeParamsAsTypes;
      _1895_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1896_typeParam) => {
        return RAST.__default.RawType((_1896_typeParam).dtor_content);
      })), _1878_sTypeParams);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1894_struct));
      Dafny.ISequence<RAST._IImplMember> _1897_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1898_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out31;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out32;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(path)), _1877_typeParamsSet, out _out31, out _out32);
      _1897_implBodyRaw = _out31;
      _1898_traitBodies = _out32;
      Dafny.ISequence<RAST._IImplMember> _1899_implBody;
      _1899_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(DCOMP.__default.escapeIdent((c).dtor_name), _1883_fieldInits))))), _1897_implBodyRaw);
      RAST._IImpl _1900_i;
      _1900_i = RAST.Impl.create_Impl(_1879_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1895_typeParamsAsTypes), _1880_whereConstraints, _1899_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1900_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1901_i;
        _1901_i = BigInteger.Zero;
        while ((_1901_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1902_superClass;
          _1902_superClass = ((c).dtor_superClasses).Select(_1901_i);
          DAST._IType _source57 = _1902_superClass;
          if (_source57.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1903___mcc_h1 = _source57.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1904___mcc_h2 = _source57.dtor_typeArgs;
            DAST._IResolvedType _1905___mcc_h3 = _source57.dtor_resolved;
            DAST._IResolvedType _source58 = _1905___mcc_h3;
            if (_source58.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1906___mcc_h7 = _source58.dtor_path;
            } else if (_source58.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1907___mcc_h9 = _source58.dtor_path;
              Dafny.ISequence<DAST._IType> _1908_typeArgs = _1904___mcc_h2;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1909_traitPath = _1903___mcc_h1;
              {
                Dafny.ISequence<Dafny.Rune> _1910_pathStr;
                Dafny.ISequence<Dafny.Rune> _out33;
                _out33 = DCOMP.COMP.GenPath(_1909_traitPath);
                _1910_pathStr = _out33;
                Dafny.ISequence<RAST._IType> _1911_typeArgs;
                Dafny.ISequence<RAST._IType> _out34;
                _out34 = (this).GenTypeArgs(_1908_typeArgs, false, false);
                _1911_typeArgs = _out34;
                Dafny.ISequence<RAST._IImplMember> _1912_body;
                _1912_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1898_traitBodies).Contains(_1909_traitPath)) {
                  _1912_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1898_traitBodies,_1909_traitPath);
                }
                Dafny.ISequence<Dafny.Rune> _1913_genSelfPath;
                Dafny.ISequence<Dafny.Rune> _out35;
                _out35 = DCOMP.COMP.GenPath(path);
                _1913_genSelfPath = _out35;
                RAST._IModDecl _1914_x;
                _1914_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1879_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1910_pathStr), _1911_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1913_genSelfPath), _1895_typeParamsAsTypes)), _1880_whereConstraints, _1912_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1914_x));
              }
            } else {
              DAST._IType _1915___mcc_h11 = _source58.dtor_baseType;
              DAST._INewtypeRange _1916___mcc_h12 = _source58.dtor_range;
              bool _1917___mcc_h13 = _source58.dtor_erase;
            }
          } else if (_source57.is_Nullable) {
            DAST._IType _1918___mcc_h17 = _source57.dtor_Nullable_a0;
          } else if (_source57.is_Tuple) {
            Dafny.ISequence<DAST._IType> _1919___mcc_h19 = _source57.dtor_Tuple_a0;
          } else if (_source57.is_Array) {
            DAST._IType _1920___mcc_h21 = _source57.dtor_element;
            BigInteger _1921___mcc_h22 = _source57.dtor_dims;
          } else if (_source57.is_Seq) {
            DAST._IType _1922___mcc_h25 = _source57.dtor_element;
          } else if (_source57.is_Set) {
            DAST._IType _1923___mcc_h27 = _source57.dtor_element;
          } else if (_source57.is_Multiset) {
            DAST._IType _1924___mcc_h29 = _source57.dtor_element;
          } else if (_source57.is_Map) {
            DAST._IType _1925___mcc_h31 = _source57.dtor_key;
            DAST._IType _1926___mcc_h32 = _source57.dtor_value;
          } else if (_source57.is_SetBuilder) {
            DAST._IType _1927___mcc_h35 = _source57.dtor_element;
          } else if (_source57.is_MapBuilder) {
            DAST._IType _1928___mcc_h37 = _source57.dtor_key;
            DAST._IType _1929___mcc_h38 = _source57.dtor_value;
          } else if (_source57.is_Arrow) {
            Dafny.ISequence<DAST._IType> _1930___mcc_h41 = _source57.dtor_args;
            DAST._IType _1931___mcc_h42 = _source57.dtor_result;
          } else if (_source57.is_Primitive) {
            DAST._IPrimitive _1932___mcc_h45 = _source57.dtor_Primitive_a0;
          } else if (_source57.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1933___mcc_h47 = _source57.dtor_Passthrough_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _1934___mcc_h49 = _source57.dtor_TypeArg_a0;
          }
          _1901_i = (_1901_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1935_d;
      _1935_d = RAST.Impl.create_ImplFor(_1879_sConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1895_typeParamsAsTypes), _1880_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1936_defaultImpl;
      _1936_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1935_d));
      RAST._IImpl _1937_p;
      _1937_p = RAST.Impl.create_ImplFor(_1879_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1895_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), ((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1938_printImpl;
      _1938_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1937_p));
      RAST._IImpl _1939_pp;
      _1939_pp = RAST.Impl.create_ImplFor(_1878_sTypeParams, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1895_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.Self)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1940_ptrPartialEqImpl;
      _1940_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1939_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1936_defaultImpl), _1938_printImpl), _1940_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1941_typeParamsSet;
      _1941_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._IType> _1942_typeParams;
      _1942_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1943_tpI;
      _1943_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1943_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._IType _1944_tp;
          _1944_tp = ((t).dtor_typeParams).Select(_1943_tpI);
          _1941_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1941_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1944_tp));
          RAST._IType _1945_genTp;
          RAST._IType _out36;
          _out36 = (this).GenType(_1944_tp, false, false);
          _1945_genTp = _out36;
          _1942_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1942_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1945_genTp));
          _1943_tpI = (_1943_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1946_fullPath;
      _1946_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1947_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1948___v34;
      Dafny.ISequence<RAST._IImplMember> _out37;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out38;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1946_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1946_fullPath)), _1941_typeParamsSet, out _out37, out _out38);
      _1947_implBody = _out37;
      _1948___v34 = _out38;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(Dafny.Sequence<RAST._ITypeParam>.FromElements(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((t).dtor_name)), _1942_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1947_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1949_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1950_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1951_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1952_whereConstraints;
      Dafny.ISet<DAST._IType> _out39;
      Dafny.ISequence<RAST._ITypeParam> _out40;
      Dafny.ISequence<RAST._ITypeParam> _out41;
      Dafny.ISequence<Dafny.Rune> _out42;
      (this).GenTypeParameters((c).dtor_typeParams, out _out39, out _out40, out _out41, out _out42);
      _1949_typeParamsSet = _out39;
      _1950_sTypeParams = _out40;
      _1951_sConstrainedTypeParams = _out41;
      _1952_whereConstraints = _out42;
      Dafny.ISequence<RAST._IType> _1953_typeParamsAsTypes;
      _1953_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1954_t) => {
        return RAST.__default.RawType((_1954_t).dtor_content);
      })), _1950_sTypeParams);
      Dafny.ISequence<Dafny.Rune> _1955_constrainedTypeParams;
      _1955_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1951_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1956_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source59 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      if (_source59.is_None) {
        RAST._IType _out43;
        _out43 = (this).GenType((c).dtor_base, false, false);
        _1956_underlyingType = _out43;
      } else {
        RAST._IType _1957___mcc_h0 = _source59.dtor_value;
        RAST._IType _1958_v = _1957___mcc_h0;
        _1956_underlyingType = _1958_v;
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), DCOMP.__default.escapeIdent((c).dtor_name), _1950_sTypeParams, RAST.Formals.create_NamelessFormals(Dafny.Sequence<RAST._INamelessFormal>.FromElements(RAST.NamelessFormal.create(RAST.Visibility.create_PUB(), _1956_underlyingType))))));
      Dafny.ISequence<Dafny.Rune> _1959_fnBody;
      _1959_fnBody = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Std.Wrappers._IOption<DAST._IExpression> _source60 = (c).dtor_witnessExpr;
      if (_source60.is_None) {
        {
          _1959_fnBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1959_fnBody, DCOMP.__default.escapeIdent((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(::std::default::Default::default())"));
        }
      } else {
        DAST._IExpression _1960___mcc_h1 = _source60.dtor_value;
        DAST._IExpression _1961_e = _1960___mcc_h1;
        {
          RAST._IExpr _1962_eStr;
          DCOMP._IOwnership _1963___v35;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964___v36;
          RAST._IExpr _out44;
          DCOMP._IOwnership _out45;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out46;
          (this).GenExpr(_1961_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out44, out _out45, out _out46);
          _1962_eStr = _out44;
          _1963___v35 = _out45;
          _1964___v36 = _out46;
          _1959_fnBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1959_fnBody, DCOMP.__default.escapeIdent((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1962_eStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
        }
      }
      RAST._IImplMember _1965_body;
      _1965_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(_1959_fnBody))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1951_sConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1953_typeParamsAsTypes), _1952_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1965_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1951_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1953_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1951_sConstrainedTypeParams, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1953_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1956_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&Self::Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1966_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1967_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1968_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1969_whereConstraints;
      Dafny.ISet<DAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParam> _out48;
      Dafny.ISequence<RAST._ITypeParam> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1966_typeParamsSet = _out47;
      _1967_sTypeParams = _out48;
      _1968_sConstrainedTypeParams = _out49;
      _1969_whereConstraints = _out50;
      Dafny.ISequence<RAST._IType> _1970_typeParamsAsTypes;
      _1970_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1971_t) => {
        return RAST.__default.RawType((_1971_t).dtor_content);
      })), _1967_sTypeParams);
      Dafny.ISequence<Dafny.Rune> _1972_constrainedTypeParams;
      _1972_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1968_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.IND, DCOMP.__default.IND));
      Dafny.ISequence<RAST._IEnumCase> _1973_ctors;
      _1973_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _1974_i;
      _1974_i = BigInteger.Zero;
      while ((_1974_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1975_ctor;
        _1975_ctor = ((c).dtor_ctors).Select(_1974_i);
        Dafny.ISequence<RAST._IFormal> _1976_ctorArgs;
        _1976_ctorArgs = Dafny.Sequence<RAST._IFormal>.FromElements();
        BigInteger _1977_j;
        _1977_j = BigInteger.Zero;
        while ((_1977_j) < (new BigInteger(((_1975_ctor).dtor_args).Count))) {
          DAST._IFormal _1978_formal;
          _1978_formal = ((_1975_ctor).dtor_args).Select(_1977_j);
          RAST._IType _1979_formalType;
          RAST._IType _out51;
          _out51 = (this).GenType((_1978_formal).dtor_typ, false, false);
          _1979_formalType = _out51;
          if ((c).dtor_isCo) {
            _1976_ctorArgs = Dafny.Sequence<RAST._IFormal>.Concat(_1976_ctorArgs, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1978_formal).dtor_name), RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1979_formalType)))));
          } else {
            _1976_ctorArgs = Dafny.Sequence<RAST._IFormal>.Concat(_1976_ctorArgs, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1978_formal).dtor_name), _1979_formalType)));
          }
          _1977_j = (_1977_j) + (BigInteger.One);
        }
        _1973_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1973_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeIdent((_1975_ctor).dtor_name), RAST.Formals.create_NamedFormals(_1976_ctorArgs))));
        _1974_i = (_1974_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1980_selfPath;
      _1980_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1981_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1982_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out52;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out53;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(_1980_selfPath)), _1966_typeParamsSet, out _out52, out _out53);
      _1981_implBodyRaw = _out52;
      _1982_traitBodies = _out53;
      Dafny.ISequence<RAST._IImplMember> _1983_implBody;
      _1983_implBody = _1981_implBodyRaw;
      _1974_i = BigInteger.Zero;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_emittedFields;
      _1984_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      while ((_1974_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1985_ctor;
        _1985_ctor = ((c).dtor_ctors).Select(_1974_i);
        BigInteger _1986_j;
        _1986_j = BigInteger.Zero;
        while ((_1986_j) < (new BigInteger(((_1985_ctor).dtor_args).Count))) {
          DAST._IFormal _1987_formal;
          _1987_formal = ((_1985_ctor).dtor_args).Select(_1986_j);
          if (!((_1984_emittedFields).Contains((_1987_formal).dtor_name))) {
            _1984_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1984_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1987_formal).dtor_name));
            RAST._IType _1988_formalType;
            RAST._IType _out54;
            _out54 = (this).GenType((_1987_formal).dtor_typ, false, false);
            _1988_formalType = _out54;
            Dafny.ISequence<RAST._IMatchCase> _1989_cases;
            _1989_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _1990_k;
            _1990_k = BigInteger.Zero;
            while ((_1990_k) < (new BigInteger(((c).dtor_ctors).Count))) {
              DAST._IDatatypeCtor _1991_ctor2;
              _1991_ctor2 = ((c).dtor_ctors).Select(_1990_k);
              Dafny.ISequence<Dafny.Rune> _1992_pattern;
              _1992_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent((_1991_ctor2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              Dafny.ISequence<Dafny.Rune> _1993_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              BigInteger _1994_l;
              _1994_l = BigInteger.Zero;
              bool _1995_hasMatchingField;
              _1995_hasMatchingField = false;
              while ((_1994_l) < (new BigInteger(((_1991_ctor2).dtor_args).Count))) {
                DAST._IFormal _1996_formal2;
                _1996_formal2 = ((_1991_ctor2).dtor_args).Select(_1994_l);
                if (((_1987_formal).dtor_name).Equals((_1996_formal2).dtor_name)) {
                  _1995_hasMatchingField = true;
                }
                _1992_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1992_pattern, DCOMP.__default.escapeIdent((_1996_formal2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _1994_l = (_1994_l) + (BigInteger.One);
              }
              _1992_pattern = Dafny.Sequence<Dafny.Rune>.Concat(_1992_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              if (_1995_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _1993_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), DCOMP.__default.escapeIdent((_1987_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1993_rhs = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((_1987_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1993_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1997_ctorMatch;
              _1997_ctorMatch = RAST.MatchCase.create(_1992_pattern, RAST.Expr.create_RawExpr(_1993_rhs));
              _1989_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1989_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1997_ctorMatch));
              _1990_k = (_1990_k) + (BigInteger.One);
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1989_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1989_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1998_methodBody;
            _1998_methodBody = RAST.Expr.create_Match(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")), _1989_cases);
            _1983_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1983_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(DCOMP.__default.escapeIdent((_1987_formal).dtor_name), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1988_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1998_methodBody)))));
          }
          _1986_j = (_1986_j) + (BigInteger.One);
        }
        _1974_i = (_1974_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _1999_typeI;
        _1999_typeI = BigInteger.Zero;
        Dafny.ISequence<RAST._IType> _2000_types;
        _2000_types = Dafny.Sequence<RAST._IType>.FromElements();
        while ((_1999_typeI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          RAST._IType _2001_genTp;
          RAST._IType _out55;
          _out55 = (this).GenType(((c).dtor_typeParams).Select(_1999_typeI), false, false);
          _2001_genTp = _out55;
          _2000_types = Dafny.Sequence<RAST._IType>.Concat(_2000_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData::")), Dafny.Sequence<RAST._IType>.FromElements(_2001_genTp))));
          _1999_typeI = (_1999_typeI) + (BigInteger.One);
        }
        _1973_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1973_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Formals.create_NamelessFormals(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessFormal>(((System.Func<RAST._IType, RAST._INamelessFormal>)((_2002_tpe) => {
  return RAST.NamelessFormal.create(RAST.Visibility.create_PRIV(), _2002_tpe);
})), _2000_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _2003_enumBody;
      _2003_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq)]")), DCOMP.__default.escapeIdent((c).dtor_name), _1967_sTypeParams, _1973_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1968_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1970_typeParamsAsTypes), _1969_whereConstraints, _1983_implBody)));
      _1974_i = BigInteger.Zero;
      Dafny.ISequence<RAST._IMatchCase> _2004_printImplBodyCases;
      _2004_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      while ((_1974_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _2005_ctor;
        _2005_ctor = ((c).dtor_ctors).Select(_1974_i);
        Dafny.ISequence<Dafny.Rune> _2006_ctorMatch;
        _2006_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((_2005_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _2007_modulePrefix;
        _2007_modulePrefix = (((((c).dtor_enclosingModule)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(((c).dtor_enclosingModule), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        RAST._IExpr _2008_printRhs;
        _2008_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _2007_modulePrefix), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent((_2005_ctor).dtor_name)), (((_2005_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        BigInteger _2009_j;
        _2009_j = BigInteger.Zero;
        while ((_2009_j) < (new BigInteger(((_2005_ctor).dtor_args).Count))) {
          DAST._IFormal _2010_formal;
          _2010_formal = ((_2005_ctor).dtor_args).Select(_2009_j);
          _2006_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2006_ctorMatch, DCOMP.__default.escapeIdent((_2010_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_2009_j).Sign == 1) {
            _2008_printRhs = (_2008_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _2008_printRhs = (_2008_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), DCOMP.__default.escapeIdent((_2010_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
          _2009_j = (_2009_j) + (BigInteger.One);
        }
        _2006_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_2006_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_2005_ctor).dtor_hasAnyArgs) {
          _2008_printRhs = (_2008_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _2008_printRhs = (_2008_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _2004_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2004_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2006_ctorMatch), RAST.Expr.create_Block(_2008_printRhs))));
        _1974_i = (_1974_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _2004_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2004_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      RAST._IExpr _2011_printImplBody;
      _2011_printImplBody = RAST.Expr.create_Match(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")), _2004_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _2012_printImpl;
      _2012_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1968_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1970_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2011_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _2013_defaultImpl;
      _2013_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        _1974_i = BigInteger.Zero;
        Dafny.ISequence<Dafny.Rune> _2014_structName;
        _2014_structName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _2015_structAssignments;
        _2015_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        while ((_1974_i) < (new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count))) {
          DAST._IFormal _2016_formal;
          _2016_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1974_i);
          _2015_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2015_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent((_2016_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
          _1974_i = (_1974_i) + (BigInteger.One);
        }
        Dafny.ISequence<RAST._ITypeParam> _2017_defaultConstrainedTypeParams;
        _2017_defaultConstrainedTypeParams = RAST.TypeParam.AddConstraintsMultiple(_1967_sTypeParams, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        _2013_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2017_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1970_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_2014_structName, _2015_structAssignments))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_2003_enumBody, _2012_printImpl), _2013_defaultImpl);
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
        BigInteger _2018_i;
        _2018_i = BigInteger.Zero;
        while ((_2018_i) < (new BigInteger((p).Count))) {
          if ((_2018_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeIdent(((p).Select(_2018_i))));
          _2018_i = (_2018_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _2019_i;
        _2019_i = BigInteger.Zero;
        while ((_2019_i) < (new BigInteger((args).Count))) {
          RAST._IType _2020_genTp;
          RAST._IType _out56;
          _out56 = (this).GenType((args).Select(_2019_i), inBinding, inFn);
          _2020_genTp = _out56;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_2020_genTp));
          _2019_i = (_2019_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public RAST._IType GenType(DAST._IType c, bool inBinding, bool inFn)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source61 = c;
      if (_source61.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2021___mcc_h0 = _source61.dtor_Path_a0;
        Dafny.ISequence<DAST._IType> _2022___mcc_h1 = _source61.dtor_typeArgs;
        DAST._IResolvedType _2023___mcc_h2 = _source61.dtor_resolved;
        DAST._IResolvedType _2024_resolved = _2023___mcc_h2;
        Dafny.ISequence<DAST._IType> _2025_args = _2022___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2026_p = _2021___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _2027_t;
          Dafny.ISequence<Dafny.Rune> _out57;
          _out57 = DCOMP.COMP.GenPath(_2026_p);
          _2027_t = _out57;
          s = RAST.Type.create_TIdentifier(_2027_t);
          Dafny.ISequence<RAST._IType> _2028_typeArgs;
          Dafny.ISequence<RAST._IType> _out58;
          _out58 = (this).GenTypeArgs(_2025_args, inBinding, inFn);
          _2028_typeArgs = _out58;
          s = RAST.Type.create_TypeApp(s, _2028_typeArgs);
          DAST._IResolvedType _source62 = _2024_resolved;
          if (_source62.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2029___mcc_h21 = _source62.dtor_path;
            {
              s = RAST.__default.Rc(s);
            }
          } else if (_source62.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2030___mcc_h22 = _source62.dtor_path;
            {
              if ((_2026_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
            DAST._IType _2031___mcc_h23 = _source62.dtor_baseType;
            DAST._INewtypeRange _2032___mcc_h24 = _source62.dtor_range;
            bool _2033___mcc_h25 = _source62.dtor_erase;
            bool _2034_erased = _2033___mcc_h25;
            DAST._INewtypeRange _2035_range = _2032___mcc_h24;
            DAST._IType _2036_t = _2031___mcc_h23;
            {
              if (_2034_erased) {
                Std.Wrappers._IOption<RAST._IType> _source63 = DCOMP.COMP.NewtypeToRustType(_2036_t, _2035_range);
                if (_source63.is_None) {
                } else {
                  RAST._IType _2037___mcc_h26 = _source63.dtor_value;
                  RAST._IType _2038_v = _2037___mcc_h26;
                  s = _2038_v;
                }
              }
            }
          }
        }
      } else if (_source61.is_Nullable) {
        DAST._IType _2039___mcc_h3 = _source61.dtor_Nullable_a0;
        DAST._IType _2040_inner = _2039___mcc_h3;
        {
          RAST._IType _2041_innerExpr;
          RAST._IType _out59;
          _out59 = (this).GenType(_2040_inner, inBinding, inFn);
          _2041_innerExpr = _out59;
          s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_2041_innerExpr));
        }
      } else if (_source61.is_Tuple) {
        Dafny.ISequence<DAST._IType> _2042___mcc_h4 = _source61.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IType> _2043_types = _2042___mcc_h4;
        {
          Dafny.ISequence<RAST._IType> _2044_args;
          _2044_args = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2045_i;
          _2045_i = BigInteger.Zero;
          while ((_2045_i) < (new BigInteger((_2043_types).Count))) {
            RAST._IType _2046_generated;
            RAST._IType _out60;
            _out60 = (this).GenType((_2043_types).Select(_2045_i), inBinding, inFn);
            _2046_generated = _out60;
            _2044_args = Dafny.Sequence<RAST._IType>.Concat(_2044_args, Dafny.Sequence<RAST._IType>.FromElements(_2046_generated));
            _2045_i = (_2045_i) + (BigInteger.One);
          }
          s = RAST.Type.create_TupleType(_2044_args);
        }
      } else if (_source61.is_Array) {
        DAST._IType _2047___mcc_h5 = _source61.dtor_element;
        BigInteger _2048___mcc_h6 = _source61.dtor_dims;
        BigInteger _2049_dims = _2048___mcc_h6;
        DAST._IType _2050_element = _2047___mcc_h5;
        {
          RAST._IType _2051_elem;
          RAST._IType _out61;
          _out61 = (this).GenType(_2050_element, inBinding, inFn);
          _2051_elem = _out61;
          s = _2051_elem;
          BigInteger _2052_i;
          _2052_i = BigInteger.Zero;
          while ((_2052_i) < (_2049_dims)) {
            s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
            _2052_i = (_2052_i) + (BigInteger.One);
          }
        }
      } else if (_source61.is_Seq) {
        DAST._IType _2053___mcc_h7 = _source61.dtor_element;
        DAST._IType _2054_element = _2053___mcc_h7;
        {
          RAST._IType _2055_elem;
          RAST._IType _out62;
          _out62 = (this).GenType(_2054_element, inBinding, inFn);
          _2055_elem = _out62;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_2055_elem));
        }
      } else if (_source61.is_Set) {
        DAST._IType _2056___mcc_h8 = _source61.dtor_element;
        DAST._IType _2057_element = _2056___mcc_h8;
        {
          RAST._IType _2058_elem;
          RAST._IType _out63;
          _out63 = (this).GenType(_2057_element, inBinding, inFn);
          _2058_elem = _out63;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_2058_elem));
        }
      } else if (_source61.is_Multiset) {
        DAST._IType _2059___mcc_h9 = _source61.dtor_element;
        DAST._IType _2060_element = _2059___mcc_h9;
        {
          RAST._IType _2061_elem;
          RAST._IType _out64;
          _out64 = (this).GenType(_2060_element, inBinding, inFn);
          _2061_elem = _out64;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_2061_elem));
        }
      } else if (_source61.is_Map) {
        DAST._IType _2062___mcc_h10 = _source61.dtor_key;
        DAST._IType _2063___mcc_h11 = _source61.dtor_value;
        DAST._IType _2064_value = _2063___mcc_h11;
        DAST._IType _2065_key = _2062___mcc_h10;
        {
          RAST._IType _2066_keyType;
          RAST._IType _out65;
          _out65 = (this).GenType(_2065_key, inBinding, inFn);
          _2066_keyType = _out65;
          RAST._IType _2067_valueType;
          RAST._IType _out66;
          _out66 = (this).GenType(_2064_value, inBinding, inFn);
          _2067_valueType = _out66;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_2066_keyType, _2067_valueType));
        }
      } else if (_source61.is_SetBuilder) {
        DAST._IType _2068___mcc_h12 = _source61.dtor_element;
        DAST._IType _2069_elem = _2068___mcc_h12;
        {
          RAST._IType _2070_elemType;
          RAST._IType _out67;
          _out67 = (this).GenType(_2069_elem, inBinding, inFn);
          _2070_elemType = _out67;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2070_elemType));
        }
      } else if (_source61.is_MapBuilder) {
        DAST._IType _2071___mcc_h13 = _source61.dtor_key;
        DAST._IType _2072___mcc_h14 = _source61.dtor_value;
        DAST._IType _2073_value = _2072___mcc_h14;
        DAST._IType _2074_key = _2071___mcc_h13;
        {
          RAST._IType _2075_keyType;
          RAST._IType _out68;
          _out68 = (this).GenType(_2074_key, inBinding, inFn);
          _2075_keyType = _out68;
          RAST._IType _2076_valueType;
          RAST._IType _out69;
          _out69 = (this).GenType(_2073_value, inBinding, inFn);
          _2076_valueType = _out69;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2075_keyType, _2076_valueType));
        }
      } else if (_source61.is_Arrow) {
        Dafny.ISequence<DAST._IType> _2077___mcc_h15 = _source61.dtor_args;
        DAST._IType _2078___mcc_h16 = _source61.dtor_result;
        DAST._IType _2079_result = _2078___mcc_h16;
        Dafny.ISequence<DAST._IType> _2080_args = _2077___mcc_h15;
        {
          Dafny.ISequence<RAST._IType> _2081_argTypes;
          _2081_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2082_i;
          _2082_i = BigInteger.Zero;
          while ((_2082_i) < (new BigInteger((_2080_args).Count))) {
            RAST._IType _2083_generated;
            RAST._IType _out70;
            _out70 = (this).GenType((_2080_args).Select(_2082_i), inBinding, true);
            _2083_generated = _out70;
            _2081_argTypes = Dafny.Sequence<RAST._IType>.Concat(_2081_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_2083_generated)));
            _2082_i = (_2082_i) + (BigInteger.One);
          }
          RAST._IType _2084_resultType;
          RAST._IType _out71;
          _out71 = (this).GenType(_2079_result, inBinding, (inFn) || (inBinding));
          _2084_resultType = _out71;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("FunctionWrapper")), Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_FnType(_2081_argTypes, RAST.Type.create_IntersectionType(_2084_resultType, RAST.__default.StaticTrait))));
        }
      } else if (_source61.is_Primitive) {
        DAST._IPrimitive _2085___mcc_h17 = _source61.dtor_Primitive_a0;
        DAST._IPrimitive _2086_p = _2085___mcc_h17;
        {
          DAST._IPrimitive _source64 = _2086_p;
          if (_source64.is_Int) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
          } else if (_source64.is_Real) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
          } else if (_source64.is_String) {
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
          } else if (_source64.is_Bool) {
            s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool"));
          } else {
            s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
          }
        }
      } else if (_source61.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _2087___mcc_h18 = _source61.dtor_Passthrough_a0;
        Dafny.ISequence<Dafny.Rune> _2088_v = _2087___mcc_h18;
        s = RAST.__default.RawType(_2088_v);
      } else {
        Dafny.ISequence<Dafny.Rune> _2089___mcc_h19 = _source61.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _source65 = _2089___mcc_h19;
        Dafny.ISequence<Dafny.Rune> _2090___mcc_h20 = _source65;
        Dafny.ISequence<Dafny.Rune> _2091_name = _2090___mcc_h20;
        s = RAST.__default.RawType(DCOMP.__default.escapeIdent(_2091_name));
      }
      return s;
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _2092_i;
      _2092_i = BigInteger.Zero;
      while ((_2092_i) < (new BigInteger((body).Count))) {
        DAST._IMethod _source66 = (body).Select(_2092_i);
        DAST._IMethod _2093___mcc_h0 = _source66;
        DAST._IMethod _2094_m = _2093___mcc_h0;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source67 = (_2094_m).dtor_overridingPath;
          if (_source67.is_None) {
            {
              RAST._IImplMember _2095_generated;
              RAST._IImplMember _out72;
              _out72 = (this).GenMethod(_2094_m, forTrait, enclosingType, enclosingTypeParams);
              _2095_generated = _out72;
              s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_2095_generated));
            }
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2096___mcc_h1 = _source67.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2097_p = _2096___mcc_h1;
            {
              Dafny.ISequence<RAST._IImplMember> _2098_existing;
              _2098_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
              if ((traitBodies).Contains(_2097_p)) {
                _2098_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_2097_p);
              }
              RAST._IImplMember _2099_genMethod;
              RAST._IImplMember _out73;
              _out73 = (this).GenMethod(_2094_m, true, enclosingType, enclosingTypeParams);
              _2099_genMethod = _out73;
              _2098_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_2098_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_2099_genMethod));
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_2097_p, _2098_existing)));
            }
          }
        }
        _2092_i = (_2092_i) + (BigInteger.One);
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _2100_i;
      _2100_i = BigInteger.Zero;
      while ((_2100_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _2101_param;
        _2101_param = (@params).Select(_2100_i);
        RAST._IType _2102_paramType;
        RAST._IType _out74;
        _out74 = (this).GenType((_2101_param).dtor_typ, false, false);
        _2102_paramType = _out74;
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_2101_param).dtor_name), RAST.Type.create_Borrowed(_2102_paramType))));
        _2100_i = (_2100_i) + (BigInteger.One);
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _2103_params;
      Dafny.ISequence<RAST._IFormal> _out75;
      _out75 = (this).GenParams((m).dtor_params);
      _2103_params = _out75;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2104_paramNames;
      _2104_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _2105_paramI;
      _2105_paramI = BigInteger.Zero;
      while ((_2105_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _2104_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2104_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_2105_paramI)).dtor_name));
        _2105_paramI = (_2105_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _2103_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), _2103_params);
        } else {
          RAST._IType _2106_tpe;
          RAST._IType _out76;
          _out76 = (this).GenType(enclosingType, false, false);
          _2106_tpe = _out76;
          _2103_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.Type.create_Borrowed(_2106_tpe))), _2103_params);
        }
      }
      Dafny.ISequence<RAST._IType> _2107_retTypeArgs;
      _2107_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _2108_typeI;
      _2108_typeI = BigInteger.Zero;
      while ((_2108_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _2109_typeExpr;
        RAST._IType _out77;
        _out77 = (this).GenType(((m).dtor_outTypes).Select(_2108_typeI), false, false);
        _2109_typeExpr = _out77;
        _2107_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2107_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2109_typeExpr));
        _2108_typeI = (_2108_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _2110_visibility;
      _2110_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<Dafny.Rune> _2111_fnName;
      _2111_fnName = DCOMP.__default.escapeIdent((m).dtor_name);
      Dafny.ISequence<DAST._IType> _2112_typeParamsFiltered;
      _2112_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _2113_typeParamI;
      _2113_typeParamI = BigInteger.Zero;
      while ((_2113_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _2114_typeParam;
        _2114_typeParam = ((m).dtor_typeParams).Select(_2113_typeParamI);
        if (!((enclosingTypeParams).Contains(_2114_typeParam))) {
          _2112_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_2112_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_2114_typeParam));
        }
        _2113_typeParamI = (_2113_typeParamI) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.Rune> _2115_whereClauses;
      _2115_whereClauses = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Dafny.ISequence<RAST._ITypeParam> _2116_typeParams;
      _2116_typeParams = Dafny.Sequence<RAST._ITypeParam>.FromElements();
      if ((new BigInteger((_2112_typeParamsFiltered).Count)).Sign == 1) {
        _2115_whereClauses = Dafny.Sequence<Dafny.Rune>.Concat(_2115_whereClauses, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" where "));
        BigInteger _2117_i;
        _2117_i = BigInteger.Zero;
        while ((_2117_i) < (new BigInteger((_2112_typeParamsFiltered).Count))) {
          RAST._IType _2118_typeExpr;
          RAST._IType _out78;
          _out78 = (this).GenType((_2112_typeParamsFiltered).Select(_2117_i), false, false);
          _2118_typeExpr = _out78;
          _2116_typeParams = Dafny.Sequence<RAST._ITypeParam>.Concat(_2116_typeParams, Dafny.Sequence<RAST._ITypeParam>.FromElements(RAST.TypeParam.create((_2118_typeExpr)._ToString(DCOMP.__default.IND), Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.CloneTrait, RAST.__default.DafnyPrintTrait, RAST.__default.DefaultTrait, RAST.__default.StaticTrait))));
          _2117_i = (_2117_i) + (BigInteger.One);
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _2119_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      if ((m).dtor_hasBody) {
        RAST._IExpr _2120_earlyReturn;
        _2120_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source68 = (m).dtor_outVars;
        if (_source68.is_None) {
        } else {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2121___mcc_h0 = _source68.dtor_value;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2122_outVars = _2121___mcc_h0;
          {
            Dafny.ISequence<RAST._IExpr> _2123_tupleArgs;
            _2123_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _2124_outI;
            _2124_outI = BigInteger.Zero;
            while ((_2124_outI) < (new BigInteger((_2122_outVars).Count))) {
              Dafny.ISequence<Dafny.Rune> _2125_outVar;
              _2125_outVar = (_2122_outVars).Select(_2124_outI);
              _2123_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2123_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent((_2125_outVar)))));
              _2124_outI = (_2124_outI) + (BigInteger.One);
            }
            _2120_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_2123_tupleArgs)));
          }
        }
        RAST._IExpr _2126_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2127___v39;
        RAST._IExpr _out79;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out80;
        (this).GenStmts((m).dtor_body, (((m).dtor_isStatic) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))), _2104_paramNames, true, _2120_earlyReturn, out _out79, out _out80);
        _2126_body = _out79;
        _2127___v39 = _out80;
        _2119_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some(_2126_body);
      } else {
        _2119_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_2110_visibility, RAST.Fn.create(_2111_fnName, _2116_typeParams, _2103_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_2107_retTypeArgs).Count)) == (BigInteger.One)) ? ((_2107_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_2107_retTypeArgs)))), _2115_whereClauses, _2119_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2128_declarations;
      _2128_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _2129_i;
      _2129_i = BigInteger.Zero;
      while ((_2129_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _2130_stmt;
        _2130_stmt = (stmts).Select(_2129_i);
        RAST._IExpr _2131_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2132_recIdents;
        RAST._IExpr _out81;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out82;
        (this).GenStmt(_2130_stmt, selfIdent, @params, (isLast) && ((_2129_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out81, out _out82);
        _2131_stmtExpr = _out81;
        _2132_recIdents = _out82;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2132_recIdents, _2128_declarations));
        DAST._IStatement _source69 = _2130_stmt;
        if (_source69.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _2133___mcc_h0 = _source69.dtor_name;
          DAST._IType _2134___mcc_h1 = _source69.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> _2135___mcc_h2 = _source69.dtor_maybeValue;
          Dafny.ISequence<Dafny.Rune> _2136_name = _2133___mcc_h0;
          {
            _2128_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2128_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2136_name));
          }
        } else if (_source69.is_Assign) {
          DAST._IAssignLhs _2137___mcc_h6 = _source69.dtor_lhs;
          DAST._IExpression _2138___mcc_h7 = _source69.dtor_value;
        } else if (_source69.is_If) {
          DAST._IExpression _2139___mcc_h10 = _source69.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2140___mcc_h11 = _source69.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _2141___mcc_h12 = _source69.dtor_els;
        } else if (_source69.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _2142___mcc_h16 = _source69.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _2143___mcc_h17 = _source69.dtor_body;
        } else if (_source69.is_While) {
          DAST._IExpression _2144___mcc_h20 = _source69.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2145___mcc_h21 = _source69.dtor_body;
        } else if (_source69.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _2146___mcc_h24 = _source69.dtor_boundName;
          DAST._IType _2147___mcc_h25 = _source69.dtor_boundType;
          DAST._IExpression _2148___mcc_h26 = _source69.dtor_over;
          Dafny.ISequence<DAST._IStatement> _2149___mcc_h27 = _source69.dtor_body;
        } else if (_source69.is_Call) {
          DAST._IExpression _2150___mcc_h32 = _source69.dtor_on;
          DAST._ICallName _2151___mcc_h33 = _source69.dtor_callName;
          Dafny.ISequence<DAST._IType> _2152___mcc_h34 = _source69.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2153___mcc_h35 = _source69.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2154___mcc_h36 = _source69.dtor_outs;
        } else if (_source69.is_Return) {
          DAST._IExpression _2155___mcc_h42 = _source69.dtor_expr;
        } else if (_source69.is_EarlyReturn) {
        } else if (_source69.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2156___mcc_h44 = _source69.dtor_toLabel;
        } else if (_source69.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _2157___mcc_h46 = _source69.dtor_body;
        } else if (_source69.is_JumpTailCallStart) {
        } else if (_source69.is_Halt) {
        } else {
          DAST._IExpression _2158___mcc_h48 = _source69.dtor_Print_a0;
        }
        generated = (generated).Then(_2131_stmtExpr);
        _2129_i = (_2129_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, Dafny.ISequence<Dafny.Rune> rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, out Dafny.ISequence<Dafny.Rune> generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IAssignLhs _source70 = lhs;
      if (_source70.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _2159___mcc_h0 = _source70.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _source71 = _2159___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _2160___mcc_h1 = _source71;
        Dafny.ISequence<Dafny.Rune> _2161_id = _2160___mcc_h1;
        {
          if ((@params).Contains(_2161_id)) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), DCOMP.__default.escapeIdent(_2161_id));
          } else {
            generated = DCOMP.__default.escapeIdent(_2161_id);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2161_id);
          needsIIFE = false;
        }
      } else if (_source70.is_Select) {
        DAST._IExpression _2162___mcc_h2 = _source70.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2163___mcc_h3 = _source70.dtor_field;
        Dafny.ISequence<Dafny.Rune> _2164_field = _2163___mcc_h3;
        DAST._IExpression _2165_on = _2162___mcc_h2;
        {
          RAST._IExpr _2166_onExpr;
          DCOMP._IOwnership _2167_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2168_recIdents;
          RAST._IExpr _out83;
          DCOMP._IOwnership _out84;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out85;
          (this).GenExpr(_2165_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out83, out _out84, out _out85);
          _2166_onExpr = _out83;
          _2167_onOwned = _out84;
          _2168_recIdents = _out85;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_2166_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _2164_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          readIdents = _2168_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _2169___mcc_h4 = _source70.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2170___mcc_h5 = _source70.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2171_indices = _2170___mcc_h5;
        DAST._IExpression _2172_on = _2169___mcc_h4;
        {
          RAST._IExpr _2173_onExpr;
          DCOMP._IOwnership _2174_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2175_recIdents;
          RAST._IExpr _out86;
          DCOMP._IOwnership _out87;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out88;
          (this).GenExpr(_2172_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out86, out _out87, out _out88);
          _2173_onExpr = _out86;
          _2174_onOwned = _out87;
          _2175_recIdents = _out88;
          readIdents = _2175_recIdents;
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _2176_i;
          _2176_i = BigInteger.Zero;
          while ((_2176_i) < (new BigInteger((_2171_indices).Count))) {
            RAST._IExpr _2177_idx;
            DCOMP._IOwnership _2178___v43;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2179_recIdentsIdx;
            RAST._IExpr _out89;
            DCOMP._IOwnership _out90;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
            (this).GenExpr((_2171_indices).Select(_2176_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out89, out _out90, out _out91);
            _2177_idx = _out89;
            _2178___v43 = _out90;
            _2179_recIdentsIdx = _out91;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_2176_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_2177_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2179_recIdentsIdx);
            _2176_i = (_2176_i) + (BigInteger.One);
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, (_2173_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _2176_i = BigInteger.Zero;
          while ((_2176_i) < (new BigInteger((_2171_indices).Count))) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_2176_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _2176_i = (_2176_i) + (BigInteger.One);
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
      DAST._IStatement _source72 = stmt;
      if (_source72.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _2180___mcc_h0 = _source72.dtor_name;
        DAST._IType _2181___mcc_h1 = _source72.dtor_typ;
        Std.Wrappers._IOption<DAST._IExpression> _2182___mcc_h2 = _source72.dtor_maybeValue;
        Std.Wrappers._IOption<DAST._IExpression> _source73 = _2182___mcc_h2;
        if (_source73.is_None) {
          DAST._IType _2183_typ = _2181___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2184_name = _2180___mcc_h0;
          {
            RAST._IType _2185_typeString;
            RAST._IType _out92;
            _out92 = (this).GenType(_2183_typ, true, false);
            _2185_typeString = _out92;
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_2184_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2185_typeString), Std.Wrappers.Option<RAST._IExpr>.create_None());
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else {
          DAST._IExpression _2186___mcc_h3 = _source73.dtor_value;
          DAST._IExpression _2187_expression = _2186___mcc_h3;
          DAST._IType _2188_typ = _2181___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2189_name = _2180___mcc_h0;
          {
            RAST._IType _2190_typeString;
            RAST._IType _out93;
            _out93 = (this).GenType(_2188_typ, true, false);
            _2190_typeString = _out93;
            RAST._IExpr _2191_expr;
            DCOMP._IOwnership _2192___v44;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2193_recIdents;
            RAST._IExpr _out94;
            DCOMP._IOwnership _out95;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
            (this).GenExpr(_2187_expression, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out94, out _out95, out _out96);
            _2191_expr = _out94;
            _2192___v44 = _out95;
            _2193_recIdents = _out96;
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_2189_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2190_typeString), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2191_expr));
            readIdents = _2193_recIdents;
          }
        }
      } else if (_source72.is_Assign) {
        DAST._IAssignLhs _2194___mcc_h4 = _source72.dtor_lhs;
        DAST._IExpression _2195___mcc_h5 = _source72.dtor_value;
        DAST._IExpression _2196_expression = _2195___mcc_h5;
        DAST._IAssignLhs _2197_lhs = _2194___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _2198_lhsGen;
          bool _2199_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2200_recIdents;
          Dafny.ISequence<Dafny.Rune> _out97;
          bool _out98;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out99;
          (this).GenAssignLhs(_2197_lhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), selfIdent, @params, out _out97, out _out98, out _out99);
          _2198_lhsGen = _out97;
          _2199_needsIIFE = _out98;
          _2200_recIdents = _out99;
          RAST._IExpr _2201_exprGen;
          DCOMP._IOwnership _2202___v45;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2203_exprIdents;
          RAST._IExpr _out100;
          DCOMP._IOwnership _out101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
          (this).GenExpr(_2196_expression, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out100, out _out101, out _out102);
          _2201_exprGen = _out100;
          _2202___v45 = _out101;
          _2203_exprIdents = _out102;
          if (_2199_needsIIFE) {
            generated = RAST.Expr.create_Block(RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2201_exprGen)), RAST.Expr.create_RawExpr(_2198_lhsGen)));
          } else {
            generated = RAST.Expr.create_AssignVar(_2198_lhsGen, _2201_exprGen);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2200_recIdents, _2203_exprIdents);
        }
      } else if (_source72.is_If) {
        DAST._IExpression _2204___mcc_h6 = _source72.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2205___mcc_h7 = _source72.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _2206___mcc_h8 = _source72.dtor_els;
        Dafny.ISequence<DAST._IStatement> _2207_els = _2206___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _2208_thn = _2205___mcc_h7;
        DAST._IExpression _2209_cond = _2204___mcc_h6;
        {
          RAST._IExpr _2210_cond;
          DCOMP._IOwnership _2211___v46;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2212_recIdents;
          RAST._IExpr _out103;
          DCOMP._IOwnership _out104;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
          (this).GenExpr(_2209_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out103, out _out104, out _out105);
          _2210_cond = _out103;
          _2211___v46 = _out104;
          _2212_recIdents = _out105;
          Dafny.ISequence<Dafny.Rune> _2213_condString;
          _2213_condString = (_2210_cond)._ToString(DCOMP.__default.IND);
          readIdents = _2212_recIdents;
          RAST._IExpr _2214_thn;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2215_thnIdents;
          RAST._IExpr _out106;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
          (this).GenStmts(_2208_thn, selfIdent, @params, isLast, earlyReturn, out _out106, out _out107);
          _2214_thn = _out106;
          _2215_thnIdents = _out107;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2215_thnIdents);
          RAST._IExpr _2216_els;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2217_elsIdents;
          RAST._IExpr _out108;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out109;
          (this).GenStmts(_2207_els, selfIdent, @params, isLast, earlyReturn, out _out108, out _out109);
          _2216_els = _out108;
          _2217_elsIdents = _out109;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2217_elsIdents);
          generated = RAST.Expr.create_IfExpr(_2210_cond, _2214_thn, _2216_els);
        }
      } else if (_source72.is_Labeled) {
        Dafny.ISequence<Dafny.Rune> _2218___mcc_h9 = _source72.dtor_lbl;
        Dafny.ISequence<DAST._IStatement> _2219___mcc_h10 = _source72.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2220_body = _2219___mcc_h10;
        Dafny.ISequence<Dafny.Rune> _2221_lbl = _2218___mcc_h9;
        {
          RAST._IExpr _2222_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2223_bodyIdents;
          RAST._IExpr _out110;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
          (this).GenStmts(_2220_body, selfIdent, @params, isLast, earlyReturn, out _out110, out _out111);
          _2222_body = _out110;
          _2223_bodyIdents = _out111;
          readIdents = _2223_bodyIdents;
          generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2221_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_2222_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
        }
      } else if (_source72.is_While) {
        DAST._IExpression _2224___mcc_h11 = _source72.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2225___mcc_h12 = _source72.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2226_body = _2225___mcc_h12;
        DAST._IExpression _2227_cond = _2224___mcc_h11;
        {
          RAST._IExpr _2228_cond;
          DCOMP._IOwnership _2229___v47;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2230_recIdents;
          RAST._IExpr _out112;
          DCOMP._IOwnership _out113;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
          (this).GenExpr(_2227_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out112, out _out113, out _out114);
          _2228_cond = _out112;
          _2229___v47 = _out113;
          _2230_recIdents = _out114;
          readIdents = _2230_recIdents;
          RAST._IExpr _2231_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2232_bodyIdents;
          RAST._IExpr _out115;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
          (this).GenStmts(_2226_body, selfIdent, @params, false, earlyReturn, out _out115, out _out116);
          _2231_body = _out115;
          _2232_bodyIdents = _out116;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2232_bodyIdents);
          generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2228_cond), _2231_body);
        }
      } else if (_source72.is_Foreach) {
        Dafny.ISequence<Dafny.Rune> _2233___mcc_h13 = _source72.dtor_boundName;
        DAST._IType _2234___mcc_h14 = _source72.dtor_boundType;
        DAST._IExpression _2235___mcc_h15 = _source72.dtor_over;
        Dafny.ISequence<DAST._IStatement> _2236___mcc_h16 = _source72.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2237_body = _2236___mcc_h16;
        DAST._IExpression _2238_over = _2235___mcc_h15;
        DAST._IType _2239_boundType = _2234___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _2240_boundName = _2233___mcc_h13;
        {
          RAST._IExpr _2241_over;
          DCOMP._IOwnership _2242___v48;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2243_recIdents;
          RAST._IExpr _out117;
          DCOMP._IOwnership _out118;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
          (this).GenExpr(_2238_over, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out117, out _out118, out _out119);
          _2241_over = _out117;
          _2242___v48 = _out118;
          _2243_recIdents = _out119;
          RAST._IType _2244_boundTypeStr;
          RAST._IType _out120;
          _out120 = (this).GenType(_2239_boundType, false, false);
          _2244_boundTypeStr = _out120;
          readIdents = _2243_recIdents;
          RAST._IExpr _2245_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2246_bodyIdents;
          RAST._IExpr _out121;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
          (this).GenStmts(_2237_body, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2240_boundName)), false, earlyReturn, out _out121, out _out122);
          _2245_body = _out121;
          _2246_bodyIdents = _out122;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2246_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2240_boundName));
          generated = RAST.Expr.create_For(DCOMP.__default.escapeIdent(_2240_boundName), _2241_over, _2245_body);
        }
      } else if (_source72.is_Call) {
        DAST._IExpression _2247___mcc_h17 = _source72.dtor_on;
        DAST._ICallName _2248___mcc_h18 = _source72.dtor_callName;
        Dafny.ISequence<DAST._IType> _2249___mcc_h19 = _source72.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2250___mcc_h20 = _source72.dtor_args;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2251___mcc_h21 = _source72.dtor_outs;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2252_maybeOutVars = _2251___mcc_h21;
        Dafny.ISequence<DAST._IExpression> _2253_args = _2250___mcc_h20;
        Dafny.ISequence<DAST._IType> _2254_typeArgs = _2249___mcc_h19;
        DAST._ICallName _2255_name = _2248___mcc_h18;
        DAST._IExpression _2256_on = _2247___mcc_h17;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2257_typeArgString;
          _2257_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_2254_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2258_typeI;
            _2258_typeI = BigInteger.Zero;
            Dafny.ISequence<RAST._IType> _2259_typeArgsR;
            _2259_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            while ((_2258_typeI) < (new BigInteger((_2254_typeArgs).Count))) {
              RAST._IType _2260_tpe;
              RAST._IType _out123;
              _out123 = (this).GenType((_2254_typeArgs).Select(_2258_typeI), false, false);
              _2260_tpe = _out123;
              _2259_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_2259_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_2260_tpe));
              _2258_typeI = (_2258_typeI) + (BigInteger.One);
            }
            _2257_typeArgString = (RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2259_typeArgsR))._ToString(DCOMP.__default.IND);
          }
          Dafny.ISequence<Dafny.Rune> _2261_argString;
          _2261_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2262_i;
          _2262_i = BigInteger.Zero;
          while ((_2262_i) < (new BigInteger((_2253_args).Count))) {
            if ((_2262_i).Sign == 1) {
              _2261_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2261_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IExpr _2263_argExpr;
            DCOMP._IOwnership _2264_ownership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2265_argIdents;
            RAST._IExpr _out124;
            DCOMP._IOwnership _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            (this).GenExpr((_2253_args).Select(_2262_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out124, out _out125, out _out126);
            _2263_argExpr = _out124;
            _2264_ownership = _out125;
            _2265_argIdents = _out126;
            Dafny.ISequence<Dafny.Rune> _2266_argExprString;
            _2266_argExprString = (_2263_argExpr)._ToString(DCOMP.__default.IND);
            _2261_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2261_argString, _2266_argExprString);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2265_argIdents);
            _2262_i = (_2262_i) + (BigInteger.One);
          }
          RAST._IExpr _2267_onExpr;
          DCOMP._IOwnership _2268___v49;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2269_enclosingIdents;
          RAST._IExpr _out127;
          DCOMP._IOwnership _out128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out129;
          (this).GenExpr(_2256_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out127, out _out128, out _out129);
          _2267_onExpr = _out127;
          _2268___v49 = _out128;
          _2269_enclosingIdents = _out129;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2269_enclosingIdents);
          Dafny.ISequence<Dafny.Rune> _2270_enclosingString;
          _2270_enclosingString = (_2267_onExpr)._ToString(DCOMP.__default.IND);
          DAST._IExpression _source74 = _2256_on;
          if (_source74.is_Literal) {
            DAST._ILiteral _2271___mcc_h26 = _source74.dtor_Literal_a0;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2272___mcc_h28 = _source74.dtor_Ident_a0;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2273___mcc_h30 = _source74.dtor_Companion_a0;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_2270_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source74.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2274___mcc_h32 = _source74.dtor_Tuple_a0;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2275___mcc_h34 = _source74.dtor_path;
            Dafny.ISequence<DAST._IType> _2276___mcc_h35 = _source74.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2277___mcc_h36 = _source74.dtor_args;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2278___mcc_h40 = _source74.dtor_dims;
            DAST._IType _2279___mcc_h41 = _source74.dtor_typ;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2280___mcc_h44 = _source74.dtor_path;
            Dafny.ISequence<DAST._IType> _2281___mcc_h45 = _source74.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2282___mcc_h46 = _source74.dtor_variant;
            bool _2283___mcc_h47 = _source74.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2284___mcc_h48 = _source74.dtor_contents;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Convert) {
            DAST._IExpression _2285___mcc_h54 = _source74.dtor_value;
            DAST._IType _2286___mcc_h55 = _source74.dtor_from;
            DAST._IType _2287___mcc_h56 = _source74.dtor_typ;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SeqConstruct) {
            DAST._IExpression _2288___mcc_h60 = _source74.dtor_length;
            DAST._IExpression _2289___mcc_h61 = _source74.dtor_elem;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2290___mcc_h64 = _source74.dtor_elements;
            DAST._IType _2291___mcc_h65 = _source74.dtor_typ;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2292___mcc_h68 = _source74.dtor_elements;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _2293___mcc_h70 = _source74.dtor_elements;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2294___mcc_h72 = _source74.dtor_mapElems;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_MapBuilder) {
            DAST._IType _2295___mcc_h74 = _source74.dtor_keyType;
            DAST._IType _2296___mcc_h75 = _source74.dtor_valueType;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SeqUpdate) {
            DAST._IExpression _2297___mcc_h78 = _source74.dtor_expr;
            DAST._IExpression _2298___mcc_h79 = _source74.dtor_indexExpr;
            DAST._IExpression _2299___mcc_h80 = _source74.dtor_value;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_MapUpdate) {
            DAST._IExpression _2300___mcc_h84 = _source74.dtor_expr;
            DAST._IExpression _2301___mcc_h85 = _source74.dtor_indexExpr;
            DAST._IExpression _2302___mcc_h86 = _source74.dtor_value;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SetBuilder) {
            DAST._IType _2303___mcc_h90 = _source74.dtor_elemType;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_ToMultiset) {
            DAST._IExpression _2304___mcc_h92 = _source74.dtor_ToMultiset_a0;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_This) {
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Ite) {
            DAST._IExpression _2305___mcc_h94 = _source74.dtor_cond;
            DAST._IExpression _2306___mcc_h95 = _source74.dtor_thn;
            DAST._IExpression _2307___mcc_h96 = _source74.dtor_els;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_UnOp) {
            DAST._IUnaryOp _2308___mcc_h100 = _source74.dtor_unOp;
            DAST._IExpression _2309___mcc_h101 = _source74.dtor_expr;
            DAST.Format._IUnaryOpFormat _2310___mcc_h102 = _source74.dtor_format1;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_BinOp) {
            DAST._IBinOp _2311___mcc_h106 = _source74.dtor_op;
            DAST._IExpression _2312___mcc_h107 = _source74.dtor_left;
            DAST._IExpression _2313___mcc_h108 = _source74.dtor_right;
            DAST.Format._IBinaryOpFormat _2314___mcc_h109 = _source74.dtor_format2;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_ArrayLen) {
            DAST._IExpression _2315___mcc_h114 = _source74.dtor_expr;
            BigInteger _2316___mcc_h115 = _source74.dtor_dim;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_MapKeys) {
            DAST._IExpression _2317___mcc_h118 = _source74.dtor_expr;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_MapValues) {
            DAST._IExpression _2318___mcc_h120 = _source74.dtor_expr;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Select) {
            DAST._IExpression _2319___mcc_h122 = _source74.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2320___mcc_h123 = _source74.dtor_field;
            bool _2321___mcc_h124 = _source74.dtor_isConstant;
            bool _2322___mcc_h125 = _source74.dtor_onDatatype;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SelectFn) {
            DAST._IExpression _2323___mcc_h130 = _source74.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2324___mcc_h131 = _source74.dtor_field;
            bool _2325___mcc_h132 = _source74.dtor_onDatatype;
            bool _2326___mcc_h133 = _source74.dtor_isStatic;
            BigInteger _2327___mcc_h134 = _source74.dtor_arity;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Index) {
            DAST._IExpression _2328___mcc_h140 = _source74.dtor_expr;
            DAST._ICollKind _2329___mcc_h141 = _source74.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _2330___mcc_h142 = _source74.dtor_indices;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_IndexRange) {
            DAST._IExpression _2331___mcc_h146 = _source74.dtor_expr;
            bool _2332___mcc_h147 = _source74.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _2333___mcc_h148 = _source74.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _2334___mcc_h149 = _source74.dtor_high;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_TupleSelect) {
            DAST._IExpression _2335___mcc_h154 = _source74.dtor_expr;
            BigInteger _2336___mcc_h155 = _source74.dtor_index;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Call) {
            DAST._IExpression _2337___mcc_h158 = _source74.dtor_on;
            DAST._ICallName _2338___mcc_h159 = _source74.dtor_callName;
            Dafny.ISequence<DAST._IType> _2339___mcc_h160 = _source74.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2340___mcc_h161 = _source74.dtor_args;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2341___mcc_h166 = _source74.dtor_params;
            DAST._IType _2342___mcc_h167 = _source74.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2343___mcc_h168 = _source74.dtor_body;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2344___mcc_h172 = _source74.dtor_values;
            DAST._IType _2345___mcc_h173 = _source74.dtor_retType;
            DAST._IExpression _2346___mcc_h174 = _source74.dtor_expr;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2347___mcc_h178 = _source74.dtor_name;
            DAST._IType _2348___mcc_h179 = _source74.dtor_typ;
            DAST._IExpression _2349___mcc_h180 = _source74.dtor_value;
            DAST._IExpression _2350___mcc_h181 = _source74.dtor_iifeBody;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Apply) {
            DAST._IExpression _2351___mcc_h186 = _source74.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2352___mcc_h187 = _source74.dtor_args;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_TypeTest) {
            DAST._IExpression _2353___mcc_h190 = _source74.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2354___mcc_h191 = _source74.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2355___mcc_h192 = _source74.dtor_variant;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_InitializationValue) {
            DAST._IType _2356___mcc_h196 = _source74.dtor_typ;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_BoolBoundedPool) {
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SetBoundedPool) {
            DAST._IExpression _2357___mcc_h198 = _source74.dtor_of;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SeqBoundedPool) {
            DAST._IExpression _2358___mcc_h200 = _source74.dtor_of;
            bool _2359___mcc_h201 = _source74.dtor_includeDuplicates;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IExpression _2360___mcc_h204 = _source74.dtor_lo;
            DAST._IExpression _2361___mcc_h205 = _source74.dtor_hi;
            {
              _2270_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _2362_receiver;
          _2362_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source75 = _2252_maybeOutVars;
          if (_source75.is_None) {
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2363___mcc_h208 = _source75.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2364_outVars = _2363___mcc_h208;
            {
              if ((new BigInteger((_2364_outVars).Count)) > (BigInteger.One)) {
                _2362_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _2365_outI;
              _2365_outI = BigInteger.Zero;
              while ((_2365_outI) < (new BigInteger((_2364_outVars).Count))) {
                if ((_2365_outI).Sign == 1) {
                  _2362_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_2362_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _2366_outVar;
                _2366_outVar = (_2364_outVars).Select(_2365_outI);
                _2362_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_2362_receiver, (_2366_outVar));
                _2365_outI = (_2365_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_2364_outVars).Count)) > (BigInteger.One)) {
                _2362_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_2362_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          }
          Dafny.ISequence<Dafny.Rune> _2367_renderedName;
          _2367_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source76) => {
            if (_source76.is_Name) {
              Dafny.ISequence<Dafny.Rune> _2368___mcc_h209 = _source76.dtor_name;
              Dafny.ISequence<Dafny.Rune> _2369_name = _2368___mcc_h209;
              return DCOMP.__default.escapeIdent(_2369_name);
            } else if (_source76.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source76.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source76.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_2255_name);
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_2362_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_2362_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _2270_enclosingString), _2367_renderedName), _2257_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2261_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");")));
        }
      } else if (_source72.is_Return) {
        DAST._IExpression _2370___mcc_h22 = _source72.dtor_expr;
        DAST._IExpression _2371_expr = _2370___mcc_h22;
        {
          RAST._IExpr _2372_expr;
          DCOMP._IOwnership _2373___v52;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2374_recIdents;
          RAST._IExpr _out130;
          DCOMP._IOwnership _out131;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
          (this).GenExpr(_2371_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out130, out _out131, out _out132);
          _2372_expr = _out130;
          _2373___v52 = _out131;
          _2374_recIdents = _out132;
          readIdents = _2374_recIdents;
          if (isLast) {
            generated = _2372_expr;
          } else {
            generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2372_expr));
          }
        }
      } else if (_source72.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source72.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2375___mcc_h23 = _source72.dtor_toLabel;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2376_toLabel = _2375___mcc_h23;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source77 = _2376_toLabel;
          if (_source77.is_None) {
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2377___mcc_h210 = _source77.dtor_value;
            Dafny.ISequence<Dafny.Rune> _2378_lbl = _2377___mcc_h210;
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2378_lbl)));
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source72.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _2379___mcc_h24 = _source72.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2380_body = _2379___mcc_h24;
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self.clone()")))));
          }
          BigInteger _2381_paramI;
          _2381_paramI = BigInteger.Zero;
          while ((_2381_paramI) < (new BigInteger((@params).Count))) {
            Dafny.ISequence<Dafny.Rune> _2382_param;
            _2382_param = (@params).Select(_2381_paramI);
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_2382_param), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.Clone(RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent(_2382_param))))));
            _2381_paramI = (_2381_paramI) + (BigInteger.One);
          }
          RAST._IExpr _2383_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2384_bodyIdents;
          RAST._IExpr _out133;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
          (this).GenStmts(_2380_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out133, out _out134);
          _2383_body = _out133;
          _2384_bodyIdents = _out134;
          readIdents = _2384_bodyIdents;
          generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _2383_body)));
        }
      } else if (_source72.is_JumpTailCallStart) {
        {
          generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source72.is_Halt) {
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else {
        DAST._IExpression _2385___mcc_h25 = _source72.dtor_Print_a0;
        DAST._IExpression _2386_e = _2385___mcc_h25;
        {
          RAST._IExpr _2387_printedExpr;
          DCOMP._IOwnership _2388_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2389_recIdents;
          RAST._IExpr _out135;
          DCOMP._IOwnership _out136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
          (this).GenExpr(_2386_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out135, out _out136, out _out137);
          _2387_printedExpr = _out135;
          _2388_recOwnership = _out136;
          _2389_recIdents = _out137;
          Dafny.ISequence<Dafny.Rune> _2390_printedExprString;
          _2390_printedExprString = (_2387_printedExpr)._ToString(DCOMP.__default.IND);
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), _2390_printedExprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));")));
          readIdents = _2389_recIdents;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source78 = range;
      if (_source78.is_U8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
      } else if (_source78.is_I8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
      } else if (_source78.is_U16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
      } else if (_source78.is_I16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
      } else if (_source78.is_U32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
      } else if (_source78.is_I32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
      } else if (_source78.is_U64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
      } else if (_source78.is_I64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
      } else if (_source78.is_U128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
      } else if (_source78.is_I128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
      } else if (_source78.is_BigInt) {
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
      DAST._IExpression _source79 = e;
      DAST._ILiteral _2391___mcc_h0 = _source79.dtor_Literal_a0;
      DAST._ILiteral _source80 = _2391___mcc_h0;
      if (_source80.is_BoolLiteral) {
        bool _2392___mcc_h1 = _source80.dtor_BoolLiteral_a0;
        if ((_2392___mcc_h1) == (false)) {
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
      } else if (_source80.is_IntLiteral) {
        Dafny.ISequence<Dafny.Rune> _2393___mcc_h2 = _source80.dtor_IntLiteral_a0;
        DAST._IType _2394___mcc_h3 = _source80.dtor_IntLiteral_a1;
        DAST._IType _2395_t = _2394___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _2396_i = _2393___mcc_h2;
        {
          DAST._IType _source81 = _2395_t;
          if (_source81.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2397___mcc_h100 = _source81.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2398___mcc_h101 = _source81.dtor_typeArgs;
            DAST._IResolvedType _2399___mcc_h102 = _source81.dtor_resolved;
            DAST._IType _2400_o = _2395_t;
            {
              RAST._IType _2401_genType;
              RAST._IType _out144;
              _out144 = (this).GenType(_2400_o, false, false);
              _2401_genType = _out144;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2401_genType);
            }
          } else if (_source81.is_Nullable) {
            DAST._IType _2402___mcc_h106 = _source81.dtor_Nullable_a0;
            DAST._IType _2403_o = _2395_t;
            {
              RAST._IType _2404_genType;
              RAST._IType _out145;
              _out145 = (this).GenType(_2403_o, false, false);
              _2404_genType = _out145;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2404_genType);
            }
          } else if (_source81.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2405___mcc_h108 = _source81.dtor_Tuple_a0;
            DAST._IType _2406_o = _2395_t;
            {
              RAST._IType _2407_genType;
              RAST._IType _out146;
              _out146 = (this).GenType(_2406_o, false, false);
              _2407_genType = _out146;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2407_genType);
            }
          } else if (_source81.is_Array) {
            DAST._IType _2408___mcc_h110 = _source81.dtor_element;
            BigInteger _2409___mcc_h111 = _source81.dtor_dims;
            DAST._IType _2410_o = _2395_t;
            {
              RAST._IType _2411_genType;
              RAST._IType _out147;
              _out147 = (this).GenType(_2410_o, false, false);
              _2411_genType = _out147;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2411_genType);
            }
          } else if (_source81.is_Seq) {
            DAST._IType _2412___mcc_h114 = _source81.dtor_element;
            DAST._IType _2413_o = _2395_t;
            {
              RAST._IType _2414_genType;
              RAST._IType _out148;
              _out148 = (this).GenType(_2413_o, false, false);
              _2414_genType = _out148;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2414_genType);
            }
          } else if (_source81.is_Set) {
            DAST._IType _2415___mcc_h116 = _source81.dtor_element;
            DAST._IType _2416_o = _2395_t;
            {
              RAST._IType _2417_genType;
              RAST._IType _out149;
              _out149 = (this).GenType(_2416_o, false, false);
              _2417_genType = _out149;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2417_genType);
            }
          } else if (_source81.is_Multiset) {
            DAST._IType _2418___mcc_h118 = _source81.dtor_element;
            DAST._IType _2419_o = _2395_t;
            {
              RAST._IType _2420_genType;
              RAST._IType _out150;
              _out150 = (this).GenType(_2419_o, false, false);
              _2420_genType = _out150;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2420_genType);
            }
          } else if (_source81.is_Map) {
            DAST._IType _2421___mcc_h120 = _source81.dtor_key;
            DAST._IType _2422___mcc_h121 = _source81.dtor_value;
            DAST._IType _2423_o = _2395_t;
            {
              RAST._IType _2424_genType;
              RAST._IType _out151;
              _out151 = (this).GenType(_2423_o, false, false);
              _2424_genType = _out151;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2424_genType);
            }
          } else if (_source81.is_SetBuilder) {
            DAST._IType _2425___mcc_h124 = _source81.dtor_element;
            DAST._IType _2426_o = _2395_t;
            {
              RAST._IType _2427_genType;
              RAST._IType _out152;
              _out152 = (this).GenType(_2426_o, false, false);
              _2427_genType = _out152;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2427_genType);
            }
          } else if (_source81.is_MapBuilder) {
            DAST._IType _2428___mcc_h126 = _source81.dtor_key;
            DAST._IType _2429___mcc_h127 = _source81.dtor_value;
            DAST._IType _2430_o = _2395_t;
            {
              RAST._IType _2431_genType;
              RAST._IType _out153;
              _out153 = (this).GenType(_2430_o, false, false);
              _2431_genType = _out153;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2431_genType);
            }
          } else if (_source81.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2432___mcc_h130 = _source81.dtor_args;
            DAST._IType _2433___mcc_h131 = _source81.dtor_result;
            DAST._IType _2434_o = _2395_t;
            {
              RAST._IType _2435_genType;
              RAST._IType _out154;
              _out154 = (this).GenType(_2434_o, false, false);
              _2435_genType = _out154;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2435_genType);
            }
          } else if (_source81.is_Primitive) {
            DAST._IPrimitive _2436___mcc_h134 = _source81.dtor_Primitive_a0;
            DAST._IPrimitive _source82 = _2436___mcc_h134;
            if (_source82.is_Int) {
              {
                if ((new BigInteger((_2396_i).Count)) <= (new BigInteger(4))) {
                  r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(RAST.Expr.create_LiteralInt(_2396_i));
                } else {
                  r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(RAST.Expr.create_LiteralString(_2396_i, true));
                }
              }
            } else if (_source82.is_Real) {
              DAST._IType _2437_o = _2395_t;
              {
                RAST._IType _2438_genType;
                RAST._IType _out155;
                _out155 = (this).GenType(_2437_o, false, false);
                _2438_genType = _out155;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2438_genType);
              }
            } else if (_source82.is_String) {
              DAST._IType _2439_o = _2395_t;
              {
                RAST._IType _2440_genType;
                RAST._IType _out156;
                _out156 = (this).GenType(_2439_o, false, false);
                _2440_genType = _out156;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2440_genType);
              }
            } else if (_source82.is_Bool) {
              DAST._IType _2441_o = _2395_t;
              {
                RAST._IType _2442_genType;
                RAST._IType _out157;
                _out157 = (this).GenType(_2441_o, false, false);
                _2442_genType = _out157;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2442_genType);
              }
            } else {
              DAST._IType _2443_o = _2395_t;
              {
                RAST._IType _2444_genType;
                RAST._IType _out158;
                _out158 = (this).GenType(_2443_o, false, false);
                _2444_genType = _out158;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2444_genType);
              }
            }
          } else if (_source81.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2445___mcc_h136 = _source81.dtor_Passthrough_a0;
            DAST._IType _2446_o = _2395_t;
            {
              RAST._IType _2447_genType;
              RAST._IType _out159;
              _out159 = (this).GenType(_2446_o, false, false);
              _2447_genType = _out159;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2447_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2448___mcc_h138 = _source81.dtor_TypeArg_a0;
            DAST._IType _2449_o = _2395_t;
            {
              RAST._IType _2450_genType;
              RAST._IType _out160;
              _out160 = (this).GenType(_2449_o, false, false);
              _2450_genType = _out160;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2396_i), _2450_genType);
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
      } else if (_source80.is_DecLiteral) {
        Dafny.ISequence<Dafny.Rune> _2451___mcc_h4 = _source80.dtor_DecLiteral_a0;
        Dafny.ISequence<Dafny.Rune> _2452___mcc_h5 = _source80.dtor_DecLiteral_a1;
        DAST._IType _2453___mcc_h6 = _source80.dtor_DecLiteral_a2;
        DAST._IType _2454_t = _2453___mcc_h6;
        Dafny.ISequence<Dafny.Rune> _2455_d = _2452___mcc_h5;
        Dafny.ISequence<Dafny.Rune> _2456_n = _2451___mcc_h4;
        {
          DAST._IType _source83 = _2454_t;
          if (_source83.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2457___mcc_h140 = _source83.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2458___mcc_h141 = _source83.dtor_typeArgs;
            DAST._IResolvedType _2459___mcc_h142 = _source83.dtor_resolved;
            DAST._IType _2460_o = _2454_t;
            {
              RAST._IType _2461_genType;
              RAST._IType _out163;
              _out163 = (this).GenType(_2460_o, false, false);
              _2461_genType = _out163;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2461_genType);
            }
          } else if (_source83.is_Nullable) {
            DAST._IType _2462___mcc_h146 = _source83.dtor_Nullable_a0;
            DAST._IType _2463_o = _2454_t;
            {
              RAST._IType _2464_genType;
              RAST._IType _out164;
              _out164 = (this).GenType(_2463_o, false, false);
              _2464_genType = _out164;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2464_genType);
            }
          } else if (_source83.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2465___mcc_h148 = _source83.dtor_Tuple_a0;
            DAST._IType _2466_o = _2454_t;
            {
              RAST._IType _2467_genType;
              RAST._IType _out165;
              _out165 = (this).GenType(_2466_o, false, false);
              _2467_genType = _out165;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2467_genType);
            }
          } else if (_source83.is_Array) {
            DAST._IType _2468___mcc_h150 = _source83.dtor_element;
            BigInteger _2469___mcc_h151 = _source83.dtor_dims;
            DAST._IType _2470_o = _2454_t;
            {
              RAST._IType _2471_genType;
              RAST._IType _out166;
              _out166 = (this).GenType(_2470_o, false, false);
              _2471_genType = _out166;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2471_genType);
            }
          } else if (_source83.is_Seq) {
            DAST._IType _2472___mcc_h154 = _source83.dtor_element;
            DAST._IType _2473_o = _2454_t;
            {
              RAST._IType _2474_genType;
              RAST._IType _out167;
              _out167 = (this).GenType(_2473_o, false, false);
              _2474_genType = _out167;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2474_genType);
            }
          } else if (_source83.is_Set) {
            DAST._IType _2475___mcc_h156 = _source83.dtor_element;
            DAST._IType _2476_o = _2454_t;
            {
              RAST._IType _2477_genType;
              RAST._IType _out168;
              _out168 = (this).GenType(_2476_o, false, false);
              _2477_genType = _out168;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2477_genType);
            }
          } else if (_source83.is_Multiset) {
            DAST._IType _2478___mcc_h158 = _source83.dtor_element;
            DAST._IType _2479_o = _2454_t;
            {
              RAST._IType _2480_genType;
              RAST._IType _out169;
              _out169 = (this).GenType(_2479_o, false, false);
              _2480_genType = _out169;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2480_genType);
            }
          } else if (_source83.is_Map) {
            DAST._IType _2481___mcc_h160 = _source83.dtor_key;
            DAST._IType _2482___mcc_h161 = _source83.dtor_value;
            DAST._IType _2483_o = _2454_t;
            {
              RAST._IType _2484_genType;
              RAST._IType _out170;
              _out170 = (this).GenType(_2483_o, false, false);
              _2484_genType = _out170;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2484_genType);
            }
          } else if (_source83.is_SetBuilder) {
            DAST._IType _2485___mcc_h164 = _source83.dtor_element;
            DAST._IType _2486_o = _2454_t;
            {
              RAST._IType _2487_genType;
              RAST._IType _out171;
              _out171 = (this).GenType(_2486_o, false, false);
              _2487_genType = _out171;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2487_genType);
            }
          } else if (_source83.is_MapBuilder) {
            DAST._IType _2488___mcc_h166 = _source83.dtor_key;
            DAST._IType _2489___mcc_h167 = _source83.dtor_value;
            DAST._IType _2490_o = _2454_t;
            {
              RAST._IType _2491_genType;
              RAST._IType _out172;
              _out172 = (this).GenType(_2490_o, false, false);
              _2491_genType = _out172;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2491_genType);
            }
          } else if (_source83.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2492___mcc_h170 = _source83.dtor_args;
            DAST._IType _2493___mcc_h171 = _source83.dtor_result;
            DAST._IType _2494_o = _2454_t;
            {
              RAST._IType _2495_genType;
              RAST._IType _out173;
              _out173 = (this).GenType(_2494_o, false, false);
              _2495_genType = _out173;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2495_genType);
            }
          } else if (_source83.is_Primitive) {
            DAST._IPrimitive _2496___mcc_h174 = _source83.dtor_Primitive_a0;
            DAST._IPrimitive _source84 = _2496___mcc_h174;
            if (_source84.is_Int) {
              DAST._IType _2497_o = _2454_t;
              {
                RAST._IType _2498_genType;
                RAST._IType _out174;
                _out174 = (this).GenType(_2497_o, false, false);
                _2498_genType = _out174;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2498_genType);
              }
            } else if (_source84.is_Real) {
              {
                r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
              }
            } else if (_source84.is_String) {
              DAST._IType _2499_o = _2454_t;
              {
                RAST._IType _2500_genType;
                RAST._IType _out175;
                _out175 = (this).GenType(_2499_o, false, false);
                _2500_genType = _out175;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2500_genType);
              }
            } else if (_source84.is_Bool) {
              DAST._IType _2501_o = _2454_t;
              {
                RAST._IType _2502_genType;
                RAST._IType _out176;
                _out176 = (this).GenType(_2501_o, false, false);
                _2502_genType = _out176;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2502_genType);
              }
            } else {
              DAST._IType _2503_o = _2454_t;
              {
                RAST._IType _2504_genType;
                RAST._IType _out177;
                _out177 = (this).GenType(_2503_o, false, false);
                _2504_genType = _out177;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2504_genType);
              }
            }
          } else if (_source83.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2505___mcc_h176 = _source83.dtor_Passthrough_a0;
            DAST._IType _2506_o = _2454_t;
            {
              RAST._IType _2507_genType;
              RAST._IType _out178;
              _out178 = (this).GenType(_2506_o, false, false);
              _2507_genType = _out178;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2507_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2508___mcc_h178 = _source83.dtor_TypeArg_a0;
            DAST._IType _2509_o = _2454_t;
            {
              RAST._IType _2510_genType;
              RAST._IType _out179;
              _out179 = (this).GenType(_2509_o, false, false);
              _2510_genType = _out179;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2456_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2455_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2510_genType);
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
      } else if (_source80.is_StringLiteral) {
        Dafny.ISequence<Dafny.Rune> _2511___mcc_h7 = _source80.dtor_StringLiteral_a0;
        Dafny.ISequence<Dafny.Rune> _2512_l = _2511___mcc_h7;
        {
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_of"))).Apply1(RAST.Expr.create_LiteralString(_2512_l, false));
          RAST._IExpr _out182;
          DCOMP._IOwnership _out183;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out182, out _out183);
          r = _out182;
          resultingOwnership = _out183;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source80.is_CharLiteral) {
        Dafny.Rune _2513___mcc_h8 = _source80.dtor_CharLiteral_a0;
        Dafny.Rune _2514_c = _2513___mcc_h8;
        {
          r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_2514_c).Value)));
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
        DAST._IType _2515___mcc_h9 = _source80.dtor_Null_a0;
        DAST._IType _2516_tpe = _2515___mcc_h9;
        {
          RAST._IType _2517_tpeGen;
          RAST._IType _out186;
          _out186 = (this).GenType(_2516_tpe, false, false);
          _2517_tpeGen = _out186;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _2517_tpeGen);
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
      DAST._IBinOp _2518_op = _let_tmp_rhs49.dtor_op;
      DAST._IExpression _2519_lExpr = _let_tmp_rhs49.dtor_left;
      DAST._IExpression _2520_rExpr = _let_tmp_rhs49.dtor_right;
      DAST.Format._IBinaryOpFormat _2521_format = _let_tmp_rhs49.dtor_format2;
      bool _2522_becomesLeftCallsRight;
      _2522_becomesLeftCallsRight = ((System.Func<DAST._IBinOp, bool>)((_source85) => {
        if (_source85.is_Eq) {
          bool _2523___mcc_h0 = _source85.dtor_referential;
          bool _2524___mcc_h1 = _source85.dtor_nullable;
          return false;
        } else if (_source85.is_Div) {
          return false;
        } else if (_source85.is_EuclidianDiv) {
          return false;
        } else if (_source85.is_Mod) {
          return false;
        } else if (_source85.is_EuclidianMod) {
          return false;
        } else if (_source85.is_Lt) {
          return false;
        } else if (_source85.is_LtChar) {
          return false;
        } else if (_source85.is_Plus) {
          return false;
        } else if (_source85.is_Minus) {
          return false;
        } else if (_source85.is_Times) {
          return false;
        } else if (_source85.is_BitwiseAnd) {
          return false;
        } else if (_source85.is_BitwiseOr) {
          return false;
        } else if (_source85.is_BitwiseXor) {
          return false;
        } else if (_source85.is_BitwiseShiftRight) {
          return false;
        } else if (_source85.is_BitwiseShiftLeft) {
          return false;
        } else if (_source85.is_And) {
          return false;
        } else if (_source85.is_Or) {
          return false;
        } else if (_source85.is_In) {
          return false;
        } else if (_source85.is_SeqProperPrefix) {
          return false;
        } else if (_source85.is_SeqPrefix) {
          return false;
        } else if (_source85.is_SetMerge) {
          return true;
        } else if (_source85.is_SetSubtraction) {
          return true;
        } else if (_source85.is_SetIntersection) {
          return true;
        } else if (_source85.is_Subset) {
          return false;
        } else if (_source85.is_ProperSubset) {
          return false;
        } else if (_source85.is_SetDisjoint) {
          return true;
        } else if (_source85.is_MapMerge) {
          return true;
        } else if (_source85.is_MapSubtraction) {
          return true;
        } else if (_source85.is_MultisetMerge) {
          return true;
        } else if (_source85.is_MultisetSubtraction) {
          return true;
        } else if (_source85.is_MultisetIntersection) {
          return true;
        } else if (_source85.is_Submultiset) {
          return false;
        } else if (_source85.is_ProperSubmultiset) {
          return false;
        } else if (_source85.is_MultisetDisjoint) {
          return true;
        } else if (_source85.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _2525___mcc_h4 = _source85.dtor_Passthrough_a0;
          return false;
        }
      }))(_2518_op);
      bool _2526_becomesRightCallsLeft;
      _2526_becomesRightCallsLeft = ((System.Func<DAST._IBinOp, bool>)((_source86) => {
        if (_source86.is_Eq) {
          bool _2527___mcc_h6 = _source86.dtor_referential;
          bool _2528___mcc_h7 = _source86.dtor_nullable;
          return false;
        } else if (_source86.is_Div) {
          return false;
        } else if (_source86.is_EuclidianDiv) {
          return false;
        } else if (_source86.is_Mod) {
          return false;
        } else if (_source86.is_EuclidianMod) {
          return false;
        } else if (_source86.is_Lt) {
          return false;
        } else if (_source86.is_LtChar) {
          return false;
        } else if (_source86.is_Plus) {
          return false;
        } else if (_source86.is_Minus) {
          return false;
        } else if (_source86.is_Times) {
          return false;
        } else if (_source86.is_BitwiseAnd) {
          return false;
        } else if (_source86.is_BitwiseOr) {
          return false;
        } else if (_source86.is_BitwiseXor) {
          return false;
        } else if (_source86.is_BitwiseShiftRight) {
          return false;
        } else if (_source86.is_BitwiseShiftLeft) {
          return false;
        } else if (_source86.is_And) {
          return false;
        } else if (_source86.is_Or) {
          return false;
        } else if (_source86.is_In) {
          return true;
        } else if (_source86.is_SeqProperPrefix) {
          return false;
        } else if (_source86.is_SeqPrefix) {
          return false;
        } else if (_source86.is_SetMerge) {
          return false;
        } else if (_source86.is_SetSubtraction) {
          return false;
        } else if (_source86.is_SetIntersection) {
          return false;
        } else if (_source86.is_Subset) {
          return false;
        } else if (_source86.is_ProperSubset) {
          return false;
        } else if (_source86.is_SetDisjoint) {
          return false;
        } else if (_source86.is_MapMerge) {
          return false;
        } else if (_source86.is_MapSubtraction) {
          return false;
        } else if (_source86.is_MultisetMerge) {
          return false;
        } else if (_source86.is_MultisetSubtraction) {
          return false;
        } else if (_source86.is_MultisetIntersection) {
          return false;
        } else if (_source86.is_Submultiset) {
          return false;
        } else if (_source86.is_ProperSubmultiset) {
          return false;
        } else if (_source86.is_MultisetDisjoint) {
          return false;
        } else if (_source86.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2529___mcc_h10 = _source86.dtor_Passthrough_a0;
          return false;
        }
      }))(_2518_op);
      bool _2530_becomesCallLeftRight;
      _2530_becomesCallLeftRight = ((System.Func<DAST._IBinOp, bool>)((_source87) => {
        if (_source87.is_Eq) {
          bool _2531___mcc_h12 = _source87.dtor_referential;
          bool _2532___mcc_h13 = _source87.dtor_nullable;
          if ((_2531___mcc_h12) == (true)) {
            if ((_2532___mcc_h13) == (false)) {
              return true;
            } else {
              return false;
            }
          } else {
            return false;
          }
        } else if (_source87.is_Div) {
          return false;
        } else if (_source87.is_EuclidianDiv) {
          return false;
        } else if (_source87.is_Mod) {
          return false;
        } else if (_source87.is_EuclidianMod) {
          return false;
        } else if (_source87.is_Lt) {
          return false;
        } else if (_source87.is_LtChar) {
          return false;
        } else if (_source87.is_Plus) {
          return false;
        } else if (_source87.is_Minus) {
          return false;
        } else if (_source87.is_Times) {
          return false;
        } else if (_source87.is_BitwiseAnd) {
          return false;
        } else if (_source87.is_BitwiseOr) {
          return false;
        } else if (_source87.is_BitwiseXor) {
          return false;
        } else if (_source87.is_BitwiseShiftRight) {
          return false;
        } else if (_source87.is_BitwiseShiftLeft) {
          return false;
        } else if (_source87.is_And) {
          return false;
        } else if (_source87.is_Or) {
          return false;
        } else if (_source87.is_In) {
          return false;
        } else if (_source87.is_SeqProperPrefix) {
          return false;
        } else if (_source87.is_SeqPrefix) {
          return false;
        } else if (_source87.is_SetMerge) {
          return false;
        } else if (_source87.is_SetSubtraction) {
          return false;
        } else if (_source87.is_SetIntersection) {
          return false;
        } else if (_source87.is_Subset) {
          return false;
        } else if (_source87.is_ProperSubset) {
          return false;
        } else if (_source87.is_SetDisjoint) {
          return false;
        } else if (_source87.is_MapMerge) {
          return false;
        } else if (_source87.is_MapSubtraction) {
          return false;
        } else if (_source87.is_MultisetMerge) {
          return false;
        } else if (_source87.is_MultisetSubtraction) {
          return false;
        } else if (_source87.is_MultisetIntersection) {
          return false;
        } else if (_source87.is_Submultiset) {
          return false;
        } else if (_source87.is_ProperSubmultiset) {
          return false;
        } else if (_source87.is_MultisetDisjoint) {
          return false;
        } else if (_source87.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2533___mcc_h16 = _source87.dtor_Passthrough_a0;
          return false;
        }
      }))(_2518_op);
      DCOMP._IOwnership _2534_expectedLeftOwnership;
      _2534_expectedLeftOwnership = ((_2522_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_2526_becomesRightCallsLeft) || (_2530_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _2535_expectedRightOwnership;
      _2535_expectedRightOwnership = (((_2522_becomesLeftCallsRight) || (_2530_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_2526_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _2536_left;
      DCOMP._IOwnership _2537___v57;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2538_recIdentsL;
      RAST._IExpr _out189;
      DCOMP._IOwnership _out190;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
      (this).GenExpr(_2519_lExpr, selfIdent, @params, _2534_expectedLeftOwnership, out _out189, out _out190, out _out191);
      _2536_left = _out189;
      _2537___v57 = _out190;
      _2538_recIdentsL = _out191;
      RAST._IExpr _2539_right;
      DCOMP._IOwnership _2540___v58;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2541_recIdentsR;
      RAST._IExpr _out192;
      DCOMP._IOwnership _out193;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
      (this).GenExpr(_2520_rExpr, selfIdent, @params, _2535_expectedRightOwnership, out _out192, out _out193, out _out194);
      _2539_right = _out192;
      _2540___v58 = _out193;
      _2541_recIdentsR = _out194;
      DAST._IBinOp _source88 = _2518_op;
      if (_source88.is_Eq) {
        bool _2542___mcc_h18 = _source88.dtor_referential;
        bool _2543___mcc_h19 = _source88.dtor_nullable;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source89 = _2518_op;
            if (_source89.is_Eq) {
              bool _2544___mcc_h24 = _source89.dtor_referential;
              bool _2545___mcc_h25 = _source89.dtor_nullable;
              bool _2546_nullable = _2545___mcc_h25;
              bool _2547_referential = _2544___mcc_h24;
              {
                if (_2547_referential) {
                  if (_2546_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source89.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source89.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2548___mcc_h26 = _source89.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2549_op = _2548___mcc_h26;
              {
                r = RAST.Expr.create_BinaryOp(_2549_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_Div) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source90 = _2518_op;
            if (_source90.is_Eq) {
              bool _2550___mcc_h27 = _source90.dtor_referential;
              bool _2551___mcc_h28 = _source90.dtor_nullable;
              bool _2552_nullable = _2551___mcc_h28;
              bool _2553_referential = _2550___mcc_h27;
              {
                if (_2553_referential) {
                  if (_2552_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source90.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source90.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2554___mcc_h29 = _source90.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2555_op = _2554___mcc_h29;
              {
                r = RAST.Expr.create_BinaryOp(_2555_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_EuclidianDiv) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source91 = _2518_op;
            if (_source91.is_Eq) {
              bool _2556___mcc_h30 = _source91.dtor_referential;
              bool _2557___mcc_h31 = _source91.dtor_nullable;
              bool _2558_nullable = _2557___mcc_h31;
              bool _2559_referential = _2556___mcc_h30;
              {
                if (_2559_referential) {
                  if (_2558_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source91.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source91.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2560___mcc_h32 = _source91.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2561_op = _2560___mcc_h32;
              {
                r = RAST.Expr.create_BinaryOp(_2561_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_Mod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source92 = _2518_op;
            if (_source92.is_Eq) {
              bool _2562___mcc_h33 = _source92.dtor_referential;
              bool _2563___mcc_h34 = _source92.dtor_nullable;
              bool _2564_nullable = _2563___mcc_h34;
              bool _2565_referential = _2562___mcc_h33;
              {
                if (_2565_referential) {
                  if (_2564_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source92.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source92.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2566___mcc_h35 = _source92.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2567_op = _2566___mcc_h35;
              {
                r = RAST.Expr.create_BinaryOp(_2567_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_EuclidianMod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source93 = _2518_op;
            if (_source93.is_Eq) {
              bool _2568___mcc_h36 = _source93.dtor_referential;
              bool _2569___mcc_h37 = _source93.dtor_nullable;
              bool _2570_nullable = _2569___mcc_h37;
              bool _2571_referential = _2568___mcc_h36;
              {
                if (_2571_referential) {
                  if (_2570_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source93.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source93.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2572___mcc_h38 = _source93.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2573_op = _2572___mcc_h38;
              {
                r = RAST.Expr.create_BinaryOp(_2573_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_Lt) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source94 = _2518_op;
            if (_source94.is_Eq) {
              bool _2574___mcc_h39 = _source94.dtor_referential;
              bool _2575___mcc_h40 = _source94.dtor_nullable;
              bool _2576_nullable = _2575___mcc_h40;
              bool _2577_referential = _2574___mcc_h39;
              {
                if (_2577_referential) {
                  if (_2576_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source94.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source94.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2578___mcc_h41 = _source94.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2579_op = _2578___mcc_h41;
              {
                r = RAST.Expr.create_BinaryOp(_2579_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_LtChar) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source95 = _2518_op;
            if (_source95.is_Eq) {
              bool _2580___mcc_h42 = _source95.dtor_referential;
              bool _2581___mcc_h43 = _source95.dtor_nullable;
              bool _2582_nullable = _2581___mcc_h43;
              bool _2583_referential = _2580___mcc_h42;
              {
                if (_2583_referential) {
                  if (_2582_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source95.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source95.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2584___mcc_h44 = _source95.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2585_op = _2584___mcc_h44;
              {
                r = RAST.Expr.create_BinaryOp(_2585_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_Plus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source96 = _2518_op;
            if (_source96.is_Eq) {
              bool _2586___mcc_h45 = _source96.dtor_referential;
              bool _2587___mcc_h46 = _source96.dtor_nullable;
              bool _2588_nullable = _2587___mcc_h46;
              bool _2589_referential = _2586___mcc_h45;
              {
                if (_2589_referential) {
                  if (_2588_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source96.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source96.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2590___mcc_h47 = _source96.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2591_op = _2590___mcc_h47;
              {
                r = RAST.Expr.create_BinaryOp(_2591_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_Minus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source97 = _2518_op;
            if (_source97.is_Eq) {
              bool _2592___mcc_h48 = _source97.dtor_referential;
              bool _2593___mcc_h49 = _source97.dtor_nullable;
              bool _2594_nullable = _2593___mcc_h49;
              bool _2595_referential = _2592___mcc_h48;
              {
                if (_2595_referential) {
                  if (_2594_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source97.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source97.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2596___mcc_h50 = _source97.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2597_op = _2596___mcc_h50;
              {
                r = RAST.Expr.create_BinaryOp(_2597_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_Times) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source98 = _2518_op;
            if (_source98.is_Eq) {
              bool _2598___mcc_h51 = _source98.dtor_referential;
              bool _2599___mcc_h52 = _source98.dtor_nullable;
              bool _2600_nullable = _2599___mcc_h52;
              bool _2601_referential = _2598___mcc_h51;
              {
                if (_2601_referential) {
                  if (_2600_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source98.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source98.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2602___mcc_h53 = _source98.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2603_op = _2602___mcc_h53;
              {
                r = RAST.Expr.create_BinaryOp(_2603_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_BitwiseAnd) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source99 = _2518_op;
            if (_source99.is_Eq) {
              bool _2604___mcc_h54 = _source99.dtor_referential;
              bool _2605___mcc_h55 = _source99.dtor_nullable;
              bool _2606_nullable = _2605___mcc_h55;
              bool _2607_referential = _2604___mcc_h54;
              {
                if (_2607_referential) {
                  if (_2606_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source99.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source99.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2608___mcc_h56 = _source99.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2609_op = _2608___mcc_h56;
              {
                r = RAST.Expr.create_BinaryOp(_2609_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_BitwiseOr) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source100 = _2518_op;
            if (_source100.is_Eq) {
              bool _2610___mcc_h57 = _source100.dtor_referential;
              bool _2611___mcc_h58 = _source100.dtor_nullable;
              bool _2612_nullable = _2611___mcc_h58;
              bool _2613_referential = _2610___mcc_h57;
              {
                if (_2613_referential) {
                  if (_2612_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source100.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source100.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2614___mcc_h59 = _source100.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2615_op = _2614___mcc_h59;
              {
                r = RAST.Expr.create_BinaryOp(_2615_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_BitwiseXor) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source101 = _2518_op;
            if (_source101.is_Eq) {
              bool _2616___mcc_h60 = _source101.dtor_referential;
              bool _2617___mcc_h61 = _source101.dtor_nullable;
              bool _2618_nullable = _2617___mcc_h61;
              bool _2619_referential = _2616___mcc_h60;
              {
                if (_2619_referential) {
                  if (_2618_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source101.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source101.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2620___mcc_h62 = _source101.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2621_op = _2620___mcc_h62;
              {
                r = RAST.Expr.create_BinaryOp(_2621_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_BitwiseShiftRight) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source102 = _2518_op;
            if (_source102.is_Eq) {
              bool _2622___mcc_h63 = _source102.dtor_referential;
              bool _2623___mcc_h64 = _source102.dtor_nullable;
              bool _2624_nullable = _2623___mcc_h64;
              bool _2625_referential = _2622___mcc_h63;
              {
                if (_2625_referential) {
                  if (_2624_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source102.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source102.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2626___mcc_h65 = _source102.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2627_op = _2626___mcc_h65;
              {
                r = RAST.Expr.create_BinaryOp(_2627_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_BitwiseShiftLeft) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source103 = _2518_op;
            if (_source103.is_Eq) {
              bool _2628___mcc_h66 = _source103.dtor_referential;
              bool _2629___mcc_h67 = _source103.dtor_nullable;
              bool _2630_nullable = _2629___mcc_h67;
              bool _2631_referential = _2628___mcc_h66;
              {
                if (_2631_referential) {
                  if (_2630_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source103.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source103.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2632___mcc_h68 = _source103.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2633_op = _2632___mcc_h68;
              {
                r = RAST.Expr.create_BinaryOp(_2633_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_And) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source104 = _2518_op;
            if (_source104.is_Eq) {
              bool _2634___mcc_h69 = _source104.dtor_referential;
              bool _2635___mcc_h70 = _source104.dtor_nullable;
              bool _2636_nullable = _2635___mcc_h70;
              bool _2637_referential = _2634___mcc_h69;
              {
                if (_2637_referential) {
                  if (_2636_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source104.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source104.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2638___mcc_h71 = _source104.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2639_op = _2638___mcc_h71;
              {
                r = RAST.Expr.create_BinaryOp(_2639_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_Or) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source105 = _2518_op;
            if (_source105.is_Eq) {
              bool _2640___mcc_h72 = _source105.dtor_referential;
              bool _2641___mcc_h73 = _source105.dtor_nullable;
              bool _2642_nullable = _2641___mcc_h73;
              bool _2643_referential = _2640___mcc_h72;
              {
                if (_2643_referential) {
                  if (_2642_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source105.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source105.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2644___mcc_h74 = _source105.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2645_op = _2644___mcc_h74;
              {
                r = RAST.Expr.create_BinaryOp(_2645_op, _2536_left, _2539_right, _2521_format);
              }
            }
          }
        }
      } else if (_source88.is_In) {
        {
          r = ((_2539_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_2536_left);
        }
      } else if (_source88.is_SeqProperPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2536_left, _2539_right, _2521_format);
      } else if (_source88.is_SeqPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2536_left, _2539_right, _2521_format);
      } else if (_source88.is_SetMerge) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2539_right);
        }
      } else if (_source88.is_SetSubtraction) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2539_right);
        }
      } else if (_source88.is_SetIntersection) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2539_right);
        }
      } else if (_source88.is_Subset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2536_left, _2539_right, _2521_format);
        }
      } else if (_source88.is_ProperSubset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2536_left, _2539_right, _2521_format);
        }
      } else if (_source88.is_SetDisjoint) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2539_right);
        }
      } else if (_source88.is_MapMerge) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2539_right);
        }
      } else if (_source88.is_MapSubtraction) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2539_right);
        }
      } else if (_source88.is_MultisetMerge) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2539_right);
        }
      } else if (_source88.is_MultisetSubtraction) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2539_right);
        }
      } else if (_source88.is_MultisetIntersection) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2539_right);
        }
      } else if (_source88.is_Submultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2536_left, _2539_right, _2521_format);
        }
      } else if (_source88.is_ProperSubmultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2536_left, _2539_right, _2521_format);
        }
      } else if (_source88.is_MultisetDisjoint) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2539_right);
        }
      } else if (_source88.is_Concat) {
        {
          r = ((_2536_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_2539_right);
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _2646___mcc_h22 = _source88.dtor_Passthrough_a0;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2518_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2518_op), _2536_left, _2539_right, _2521_format);
          } else {
            DAST._IBinOp _source106 = _2518_op;
            if (_source106.is_Eq) {
              bool _2647___mcc_h75 = _source106.dtor_referential;
              bool _2648___mcc_h76 = _source106.dtor_nullable;
              bool _2649_nullable = _2648___mcc_h76;
              bool _2650_referential = _2647___mcc_h75;
              {
                if (_2650_referential) {
                  if (_2649_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2536_left, _2539_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source106.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else if (_source106.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2536_left, _2539_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2651___mcc_h77 = _source106.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2652_op = _2651___mcc_h77;
              {
                r = RAST.Expr.create_BinaryOp(_2652_op, _2536_left, _2539_right, _2521_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2538_recIdentsL, _2541_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs50 = e;
      DAST._IExpression _2653_expr = _let_tmp_rhs50.dtor_value;
      DAST._IType _2654_fromTpe = _let_tmp_rhs50.dtor_from;
      DAST._IType _2655_toTpe = _let_tmp_rhs50.dtor_typ;
      RAST._IExpr _2656_recursiveGen;
      DCOMP._IOwnership _2657_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2658_recIdents;
      RAST._IExpr _out197;
      DCOMP._IOwnership _out198;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out199;
      (this).GenExpr(_2653_expr, selfIdent, @params, expectedOwnership, out _out197, out _out198, out _out199);
      _2656_recursiveGen = _out197;
      _2657_recOwned = _out198;
      _2658_recIdents = _out199;
      r = _2656_recursiveGen;
      if (object.Equals(_2657_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out200;
      DCOMP._IOwnership _out201;
      DCOMP.COMP.FromOwnership(r, _2657_recOwned, expectedOwnership, out _out200, out _out201);
      r = _out200;
      resultingOwnership = _out201;
      readIdents = _2658_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs51 = e;
      DAST._IExpression _2659_expr = _let_tmp_rhs51.dtor_value;
      DAST._IType _2660_fromTpe = _let_tmp_rhs51.dtor_from;
      DAST._IType _2661_toTpe = _let_tmp_rhs51.dtor_typ;
      RAST._IExpr _2662_recursiveGen;
      DCOMP._IOwnership _2663_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2664_recIdents;
      RAST._IExpr _out202;
      DCOMP._IOwnership _out203;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
      (this).GenExpr(_2659_expr, selfIdent, @params, expectedOwnership, out _out202, out _out203, out _out204);
      _2662_recursiveGen = _out202;
      _2663_recOwned = _out203;
      _2664_recIdents = _out204;
      r = _2662_recursiveGen;
      if (object.Equals(_2663_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out205;
      DCOMP._IOwnership _out206;
      DCOMP.COMP.FromOwnership(r, _2663_recOwned, expectedOwnership, out _out205, out _out206);
      r = _out205;
      resultingOwnership = _out206;
      readIdents = _2664_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs52 = e;
      DAST._IExpression _2665_expr = _let_tmp_rhs52.dtor_value;
      DAST._IType _2666_fromTpe = _let_tmp_rhs52.dtor_from;
      DAST._IType _2667_toTpe = _let_tmp_rhs52.dtor_typ;
      DAST._IType _let_tmp_rhs53 = _2667_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2668___v60 = _let_tmp_rhs53.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _2669___v61 = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs54 = _let_tmp_rhs53.dtor_resolved;
      DAST._IType _2670_b = _let_tmp_rhs54.dtor_baseType;
      DAST._INewtypeRange _2671_range = _let_tmp_rhs54.dtor_range;
      bool _2672_erase = _let_tmp_rhs54.dtor_erase;
      if (object.Equals(_2666_fromTpe, _2670_b)) {
        RAST._IExpr _2673_recursiveGen;
        DCOMP._IOwnership _2674_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2675_recIdents;
        RAST._IExpr _out207;
        DCOMP._IOwnership _out208;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
        (this).GenExpr(_2665_expr, selfIdent, @params, expectedOwnership, out _out207, out _out208, out _out209);
        _2673_recursiveGen = _out207;
        _2674_recOwned = _out208;
        _2675_recIdents = _out209;
        Std.Wrappers._IOption<RAST._IType> _2676_potentialRhsType;
        _2676_potentialRhsType = DCOMP.COMP.NewtypeToRustType(_2670_b, _2671_range);
        Std.Wrappers._IOption<RAST._IType> _source107 = _2676_potentialRhsType;
        if (_source107.is_None) {
          if (_2672_erase) {
            r = _2673_recursiveGen;
          } else {
            RAST._IType _2677_rhsType;
            RAST._IType _out210;
            _out210 = (this).GenType(_2667_toTpe, true, false);
            _2677_rhsType = _out210;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_2677_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_2673_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out211;
          DCOMP._IOwnership _out212;
          DCOMP.COMP.FromOwnership(r, _2674_recOwned, expectedOwnership, out _out211, out _out212);
          r = _out211;
          resultingOwnership = _out212;
        } else {
          RAST._IType _2678___mcc_h0 = _source107.dtor_value;
          RAST._IType _2679_v = _2678___mcc_h0;
          r = RAST.Expr.create_ConversionNum(_2679_v, _2673_recursiveGen);
          RAST._IExpr _out213;
          DCOMP._IOwnership _out214;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out213, out _out214);
          r = _out213;
          resultingOwnership = _out214;
        }
        readIdents = _2675_recIdents;
      } else {
        RAST._IExpr _out215;
        DCOMP._IOwnership _out216;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out217;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_2665_expr, _2666_fromTpe, _2670_b), _2670_b, _2667_toTpe), selfIdent, @params, expectedOwnership, out _out215, out _out216, out _out217);
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
      DAST._IExpression _2680_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _2681_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _2682_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _2681_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2683___v62 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _2684___v63 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _2685_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _2686_range = _let_tmp_rhs57.dtor_range;
      bool _2687_erase = _let_tmp_rhs57.dtor_erase;
      if (object.Equals(_2685_b, _2682_toTpe)) {
        RAST._IExpr _2688_recursiveGen;
        DCOMP._IOwnership _2689_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2690_recIdents;
        RAST._IExpr _out218;
        DCOMP._IOwnership _out219;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out220;
        (this).GenExpr(_2680_expr, selfIdent, @params, expectedOwnership, out _out218, out _out219, out _out220);
        _2688_recursiveGen = _out218;
        _2689_recOwned = _out219;
        _2690_recIdents = _out220;
        if (_2687_erase) {
          r = _2688_recursiveGen;
        } else {
          r = (_2688_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
        }
        RAST._IExpr _out221;
        DCOMP._IOwnership _out222;
        DCOMP.COMP.FromOwnership(r, _2689_recOwned, expectedOwnership, out _out221, out _out222);
        r = _out221;
        resultingOwnership = _out222;
        readIdents = _2690_recIdents;
      } else {
        RAST._IExpr _out223;
        DCOMP._IOwnership _out224;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_2680_expr, _2681_fromTpe, _2685_b), _2685_b, _2682_toTpe), selfIdent, @params, expectedOwnership, out _out223, out _out224, out _out225);
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
      DAST._IExpression _2691_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _2692_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _2693_toTpe = _let_tmp_rhs58.dtor_typ;
      RAST._IExpr _2694_recursiveGen;
      DCOMP._IOwnership _2695_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2696_recIdents;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_2691_expr, selfIdent, @params, expectedOwnership, out _out226, out _out227, out _out228);
      _2694_recursiveGen = _out226;
      _2695_recOwned = _out227;
      _2696_recIdents = _out228;
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_2694_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)")));
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out229, out _out230);
      r = _out229;
      resultingOwnership = _out230;
      readIdents = _2696_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs59 = e;
      DAST._IExpression _2697_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _2698_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _2699_toTpe = _let_tmp_rhs59.dtor_typ;
      if (object.Equals(_2698_fromTpe, _2699_toTpe)) {
        RAST._IExpr _2700_recursiveGen;
        DCOMP._IOwnership _2701_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2702_recIdents;
        RAST._IExpr _out231;
        DCOMP._IOwnership _out232;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out233;
        (this).GenExpr(_2697_expr, selfIdent, @params, expectedOwnership, out _out231, out _out232, out _out233);
        _2700_recursiveGen = _out231;
        _2701_recOwned = _out232;
        _2702_recIdents = _out233;
        r = _2700_recursiveGen;
        RAST._IExpr _out234;
        DCOMP._IOwnership _out235;
        DCOMP.COMP.FromOwnership(r, _2701_recOwned, expectedOwnership, out _out234, out _out235);
        r = _out234;
        resultingOwnership = _out235;
        readIdents = _2702_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source108 = _System.Tuple2<DAST._IType, DAST._IType>.create(_2698_fromTpe, _2699_toTpe);
        DAST._IType _2703___mcc_h0 = _source108.dtor__0;
        DAST._IType _2704___mcc_h1 = _source108.dtor__1;
        DAST._IType _source109 = _2703___mcc_h0;
        if (_source109.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2705___mcc_h4 = _source109.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _2706___mcc_h5 = _source109.dtor_typeArgs;
          DAST._IResolvedType _2707___mcc_h6 = _source109.dtor_resolved;
          DAST._IResolvedType _source110 = _2707___mcc_h6;
          if (_source110.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2708___mcc_h16 = _source110.dtor_path;
            DAST._IType _source111 = _2704___mcc_h1;
            if (_source111.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2709___mcc_h20 = _source111.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2710___mcc_h21 = _source111.dtor_typeArgs;
              DAST._IResolvedType _2711___mcc_h22 = _source111.dtor_resolved;
              DAST._IResolvedType _source112 = _2711___mcc_h22;
              if (_source112.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2712___mcc_h26 = _source112.dtor_path;
                {
                  RAST._IExpr _out236;
                  DCOMP._IOwnership _out237;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out238;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out236, out _out237, out _out238);
                  r = _out236;
                  resultingOwnership = _out237;
                  readIdents = _out238;
                }
              } else if (_source112.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2713___mcc_h28 = _source112.dtor_path;
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
                DAST._IType _2714___mcc_h30 = _source112.dtor_baseType;
                DAST._INewtypeRange _2715___mcc_h31 = _source112.dtor_range;
                bool _2716___mcc_h32 = _source112.dtor_erase;
                bool _2717_erase = _2716___mcc_h32;
                DAST._INewtypeRange _2718_range = _2715___mcc_h31;
                DAST._IType _2719_b = _2714___mcc_h30;
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
            } else if (_source111.is_Nullable) {
              DAST._IType _2720___mcc_h36 = _source111.dtor_Nullable_a0;
              {
                RAST._IExpr _out245;
                DCOMP._IOwnership _out246;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out247;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out245, out _out246, out _out247);
                r = _out245;
                resultingOwnership = _out246;
                readIdents = _out247;
              }
            } else if (_source111.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2721___mcc_h38 = _source111.dtor_Tuple_a0;
              {
                RAST._IExpr _out248;
                DCOMP._IOwnership _out249;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out248, out _out249, out _out250);
                r = _out248;
                resultingOwnership = _out249;
                readIdents = _out250;
              }
            } else if (_source111.is_Array) {
              DAST._IType _2722___mcc_h40 = _source111.dtor_element;
              BigInteger _2723___mcc_h41 = _source111.dtor_dims;
              {
                RAST._IExpr _out251;
                DCOMP._IOwnership _out252;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out251, out _out252, out _out253);
                r = _out251;
                resultingOwnership = _out252;
                readIdents = _out253;
              }
            } else if (_source111.is_Seq) {
              DAST._IType _2724___mcc_h44 = _source111.dtor_element;
              {
                RAST._IExpr _out254;
                DCOMP._IOwnership _out255;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out256;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out254, out _out255, out _out256);
                r = _out254;
                resultingOwnership = _out255;
                readIdents = _out256;
              }
            } else if (_source111.is_Set) {
              DAST._IType _2725___mcc_h46 = _source111.dtor_element;
              {
                RAST._IExpr _out257;
                DCOMP._IOwnership _out258;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out259;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out257, out _out258, out _out259);
                r = _out257;
                resultingOwnership = _out258;
                readIdents = _out259;
              }
            } else if (_source111.is_Multiset) {
              DAST._IType _2726___mcc_h48 = _source111.dtor_element;
              {
                RAST._IExpr _out260;
                DCOMP._IOwnership _out261;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out260, out _out261, out _out262);
                r = _out260;
                resultingOwnership = _out261;
                readIdents = _out262;
              }
            } else if (_source111.is_Map) {
              DAST._IType _2727___mcc_h50 = _source111.dtor_key;
              DAST._IType _2728___mcc_h51 = _source111.dtor_value;
              {
                RAST._IExpr _out263;
                DCOMP._IOwnership _out264;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out263, out _out264, out _out265);
                r = _out263;
                resultingOwnership = _out264;
                readIdents = _out265;
              }
            } else if (_source111.is_SetBuilder) {
              DAST._IType _2729___mcc_h54 = _source111.dtor_element;
              {
                RAST._IExpr _out266;
                DCOMP._IOwnership _out267;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out268;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out266, out _out267, out _out268);
                r = _out266;
                resultingOwnership = _out267;
                readIdents = _out268;
              }
            } else if (_source111.is_MapBuilder) {
              DAST._IType _2730___mcc_h56 = _source111.dtor_key;
              DAST._IType _2731___mcc_h57 = _source111.dtor_value;
              {
                RAST._IExpr _out269;
                DCOMP._IOwnership _out270;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out269, out _out270, out _out271);
                r = _out269;
                resultingOwnership = _out270;
                readIdents = _out271;
              }
            } else if (_source111.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2732___mcc_h60 = _source111.dtor_args;
              DAST._IType _2733___mcc_h61 = _source111.dtor_result;
              {
                RAST._IExpr _out272;
                DCOMP._IOwnership _out273;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out272, out _out273, out _out274);
                r = _out272;
                resultingOwnership = _out273;
                readIdents = _out274;
              }
            } else if (_source111.is_Primitive) {
              DAST._IPrimitive _2734___mcc_h64 = _source111.dtor_Primitive_a0;
              {
                RAST._IExpr _out275;
                DCOMP._IOwnership _out276;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out275, out _out276, out _out277);
                r = _out275;
                resultingOwnership = _out276;
                readIdents = _out277;
              }
            } else if (_source111.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2735___mcc_h66 = _source111.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _2736___mcc_h68 = _source111.dtor_TypeArg_a0;
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
          } else if (_source110.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2737___mcc_h70 = _source110.dtor_path;
            DAST._IType _source113 = _2704___mcc_h1;
            if (_source113.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2738___mcc_h74 = _source113.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2739___mcc_h75 = _source113.dtor_typeArgs;
              DAST._IResolvedType _2740___mcc_h76 = _source113.dtor_resolved;
              DAST._IResolvedType _source114 = _2740___mcc_h76;
              if (_source114.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2741___mcc_h80 = _source114.dtor_path;
                {
                  RAST._IExpr _out284;
                  DCOMP._IOwnership _out285;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out284, out _out285, out _out286);
                  r = _out284;
                  resultingOwnership = _out285;
                  readIdents = _out286;
                }
              } else if (_source114.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2742___mcc_h82 = _source114.dtor_path;
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
                DAST._IType _2743___mcc_h84 = _source114.dtor_baseType;
                DAST._INewtypeRange _2744___mcc_h85 = _source114.dtor_range;
                bool _2745___mcc_h86 = _source114.dtor_erase;
                bool _2746_erase = _2745___mcc_h86;
                DAST._INewtypeRange _2747_range = _2744___mcc_h85;
                DAST._IType _2748_b = _2743___mcc_h84;
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
            } else if (_source113.is_Nullable) {
              DAST._IType _2749___mcc_h90 = _source113.dtor_Nullable_a0;
              {
                RAST._IExpr _out293;
                DCOMP._IOwnership _out294;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out295;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out293, out _out294, out _out295);
                r = _out293;
                resultingOwnership = _out294;
                readIdents = _out295;
              }
            } else if (_source113.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2750___mcc_h92 = _source113.dtor_Tuple_a0;
              {
                RAST._IExpr _out296;
                DCOMP._IOwnership _out297;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out296, out _out297, out _out298);
                r = _out296;
                resultingOwnership = _out297;
                readIdents = _out298;
              }
            } else if (_source113.is_Array) {
              DAST._IType _2751___mcc_h94 = _source113.dtor_element;
              BigInteger _2752___mcc_h95 = _source113.dtor_dims;
              {
                RAST._IExpr _out299;
                DCOMP._IOwnership _out300;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out299, out _out300, out _out301);
                r = _out299;
                resultingOwnership = _out300;
                readIdents = _out301;
              }
            } else if (_source113.is_Seq) {
              DAST._IType _2753___mcc_h98 = _source113.dtor_element;
              {
                RAST._IExpr _out302;
                DCOMP._IOwnership _out303;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out302, out _out303, out _out304);
                r = _out302;
                resultingOwnership = _out303;
                readIdents = _out304;
              }
            } else if (_source113.is_Set) {
              DAST._IType _2754___mcc_h100 = _source113.dtor_element;
              {
                RAST._IExpr _out305;
                DCOMP._IOwnership _out306;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out305, out _out306, out _out307);
                r = _out305;
                resultingOwnership = _out306;
                readIdents = _out307;
              }
            } else if (_source113.is_Multiset) {
              DAST._IType _2755___mcc_h102 = _source113.dtor_element;
              {
                RAST._IExpr _out308;
                DCOMP._IOwnership _out309;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out310;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out308, out _out309, out _out310);
                r = _out308;
                resultingOwnership = _out309;
                readIdents = _out310;
              }
            } else if (_source113.is_Map) {
              DAST._IType _2756___mcc_h104 = _source113.dtor_key;
              DAST._IType _2757___mcc_h105 = _source113.dtor_value;
              {
                RAST._IExpr _out311;
                DCOMP._IOwnership _out312;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out313;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out311, out _out312, out _out313);
                r = _out311;
                resultingOwnership = _out312;
                readIdents = _out313;
              }
            } else if (_source113.is_SetBuilder) {
              DAST._IType _2758___mcc_h108 = _source113.dtor_element;
              {
                RAST._IExpr _out314;
                DCOMP._IOwnership _out315;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out314, out _out315, out _out316);
                r = _out314;
                resultingOwnership = _out315;
                readIdents = _out316;
              }
            } else if (_source113.is_MapBuilder) {
              DAST._IType _2759___mcc_h110 = _source113.dtor_key;
              DAST._IType _2760___mcc_h111 = _source113.dtor_value;
              {
                RAST._IExpr _out317;
                DCOMP._IOwnership _out318;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out317, out _out318, out _out319);
                r = _out317;
                resultingOwnership = _out318;
                readIdents = _out319;
              }
            } else if (_source113.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2761___mcc_h114 = _source113.dtor_args;
              DAST._IType _2762___mcc_h115 = _source113.dtor_result;
              {
                RAST._IExpr _out320;
                DCOMP._IOwnership _out321;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out320, out _out321, out _out322);
                r = _out320;
                resultingOwnership = _out321;
                readIdents = _out322;
              }
            } else if (_source113.is_Primitive) {
              DAST._IPrimitive _2763___mcc_h118 = _source113.dtor_Primitive_a0;
              {
                RAST._IExpr _out323;
                DCOMP._IOwnership _out324;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out325;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out323, out _out324, out _out325);
                r = _out323;
                resultingOwnership = _out324;
                readIdents = _out325;
              }
            } else if (_source113.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2764___mcc_h120 = _source113.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _2765___mcc_h122 = _source113.dtor_TypeArg_a0;
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
            DAST._IType _2766___mcc_h124 = _source110.dtor_baseType;
            DAST._INewtypeRange _2767___mcc_h125 = _source110.dtor_range;
            bool _2768___mcc_h126 = _source110.dtor_erase;
            DAST._IType _source115 = _2704___mcc_h1;
            if (_source115.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2769___mcc_h136 = _source115.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2770___mcc_h137 = _source115.dtor_typeArgs;
              DAST._IResolvedType _2771___mcc_h138 = _source115.dtor_resolved;
              DAST._IResolvedType _source116 = _2771___mcc_h138;
              if (_source116.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2772___mcc_h145 = _source116.dtor_path;
                bool _2773_erase = _2768___mcc_h126;
                DAST._INewtypeRange _2774_range = _2767___mcc_h125;
                DAST._IType _2775_b = _2766___mcc_h124;
                {
                  RAST._IExpr _out332;
                  DCOMP._IOwnership _out333;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                  (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out332, out _out333, out _out334);
                  r = _out332;
                  resultingOwnership = _out333;
                  readIdents = _out334;
                }
              } else if (_source116.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2776___mcc_h148 = _source116.dtor_path;
                bool _2777_erase = _2768___mcc_h126;
                DAST._INewtypeRange _2778_range = _2767___mcc_h125;
                DAST._IType _2779_b = _2766___mcc_h124;
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
                DAST._IType _2780___mcc_h151 = _source116.dtor_baseType;
                DAST._INewtypeRange _2781___mcc_h152 = _source116.dtor_range;
                bool _2782___mcc_h153 = _source116.dtor_erase;
                bool _2783_erase = _2782___mcc_h153;
                DAST._INewtypeRange _2784_range = _2781___mcc_h152;
                DAST._IType _2785_b = _2780___mcc_h151;
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
            } else if (_source115.is_Nullable) {
              DAST._IType _2786___mcc_h160 = _source115.dtor_Nullable_a0;
              {
                RAST._IExpr _out341;
                DCOMP._IOwnership _out342;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out341, out _out342, out _out343);
                r = _out341;
                resultingOwnership = _out342;
                readIdents = _out343;
              }
            } else if (_source115.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2787___mcc_h163 = _source115.dtor_Tuple_a0;
              bool _2788_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2789_range = _2767___mcc_h125;
              DAST._IType _2790_b = _2766___mcc_h124;
              {
                RAST._IExpr _out344;
                DCOMP._IOwnership _out345;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out346;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out344, out _out345, out _out346);
                r = _out344;
                resultingOwnership = _out345;
                readIdents = _out346;
              }
            } else if (_source115.is_Array) {
              DAST._IType _2791___mcc_h166 = _source115.dtor_element;
              BigInteger _2792___mcc_h167 = _source115.dtor_dims;
              bool _2793_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2794_range = _2767___mcc_h125;
              DAST._IType _2795_b = _2766___mcc_h124;
              {
                RAST._IExpr _out347;
                DCOMP._IOwnership _out348;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out347, out _out348, out _out349);
                r = _out347;
                resultingOwnership = _out348;
                readIdents = _out349;
              }
            } else if (_source115.is_Seq) {
              DAST._IType _2796___mcc_h172 = _source115.dtor_element;
              bool _2797_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2798_range = _2767___mcc_h125;
              DAST._IType _2799_b = _2766___mcc_h124;
              {
                RAST._IExpr _out350;
                DCOMP._IOwnership _out351;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out350, out _out351, out _out352);
                r = _out350;
                resultingOwnership = _out351;
                readIdents = _out352;
              }
            } else if (_source115.is_Set) {
              DAST._IType _2800___mcc_h175 = _source115.dtor_element;
              bool _2801_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2802_range = _2767___mcc_h125;
              DAST._IType _2803_b = _2766___mcc_h124;
              {
                RAST._IExpr _out353;
                DCOMP._IOwnership _out354;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out353, out _out354, out _out355);
                r = _out353;
                resultingOwnership = _out354;
                readIdents = _out355;
              }
            } else if (_source115.is_Multiset) {
              DAST._IType _2804___mcc_h178 = _source115.dtor_element;
              bool _2805_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2806_range = _2767___mcc_h125;
              DAST._IType _2807_b = _2766___mcc_h124;
              {
                RAST._IExpr _out356;
                DCOMP._IOwnership _out357;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out356, out _out357, out _out358);
                r = _out356;
                resultingOwnership = _out357;
                readIdents = _out358;
              }
            } else if (_source115.is_Map) {
              DAST._IType _2808___mcc_h181 = _source115.dtor_key;
              DAST._IType _2809___mcc_h182 = _source115.dtor_value;
              bool _2810_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2811_range = _2767___mcc_h125;
              DAST._IType _2812_b = _2766___mcc_h124;
              {
                RAST._IExpr _out359;
                DCOMP._IOwnership _out360;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out359, out _out360, out _out361);
                r = _out359;
                resultingOwnership = _out360;
                readIdents = _out361;
              }
            } else if (_source115.is_SetBuilder) {
              DAST._IType _2813___mcc_h187 = _source115.dtor_element;
              bool _2814_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2815_range = _2767___mcc_h125;
              DAST._IType _2816_b = _2766___mcc_h124;
              {
                RAST._IExpr _out362;
                DCOMP._IOwnership _out363;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out362, out _out363, out _out364);
                r = _out362;
                resultingOwnership = _out363;
                readIdents = _out364;
              }
            } else if (_source115.is_MapBuilder) {
              DAST._IType _2817___mcc_h190 = _source115.dtor_key;
              DAST._IType _2818___mcc_h191 = _source115.dtor_value;
              bool _2819_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2820_range = _2767___mcc_h125;
              DAST._IType _2821_b = _2766___mcc_h124;
              {
                RAST._IExpr _out365;
                DCOMP._IOwnership _out366;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out365, out _out366, out _out367);
                r = _out365;
                resultingOwnership = _out366;
                readIdents = _out367;
              }
            } else if (_source115.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2822___mcc_h196 = _source115.dtor_args;
              DAST._IType _2823___mcc_h197 = _source115.dtor_result;
              bool _2824_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2825_range = _2767___mcc_h125;
              DAST._IType _2826_b = _2766___mcc_h124;
              {
                RAST._IExpr _out368;
                DCOMP._IOwnership _out369;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out370;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out368, out _out369, out _out370);
                r = _out368;
                resultingOwnership = _out369;
                readIdents = _out370;
              }
            } else if (_source115.is_Primitive) {
              DAST._IPrimitive _2827___mcc_h202 = _source115.dtor_Primitive_a0;
              bool _2828_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2829_range = _2767___mcc_h125;
              DAST._IType _2830_b = _2766___mcc_h124;
              {
                RAST._IExpr _out371;
                DCOMP._IOwnership _out372;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out371, out _out372, out _out373);
                r = _out371;
                resultingOwnership = _out372;
                readIdents = _out373;
              }
            } else if (_source115.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2831___mcc_h205 = _source115.dtor_Passthrough_a0;
              bool _2832_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2833_range = _2767___mcc_h125;
              DAST._IType _2834_b = _2766___mcc_h124;
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
              Dafny.ISequence<Dafny.Rune> _2835___mcc_h208 = _source115.dtor_TypeArg_a0;
              bool _2836_erase = _2768___mcc_h126;
              DAST._INewtypeRange _2837_range = _2767___mcc_h125;
              DAST._IType _2838_b = _2766___mcc_h124;
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
        } else if (_source109.is_Nullable) {
          DAST._IType _2839___mcc_h211 = _source109.dtor_Nullable_a0;
          DAST._IType _source117 = _2704___mcc_h1;
          if (_source117.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2840___mcc_h215 = _source117.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2841___mcc_h216 = _source117.dtor_typeArgs;
            DAST._IResolvedType _2842___mcc_h217 = _source117.dtor_resolved;
            DAST._IResolvedType _source118 = _2842___mcc_h217;
            if (_source118.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2843___mcc_h224 = _source118.dtor_path;
              {
                RAST._IExpr _out380;
                DCOMP._IOwnership _out381;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
                (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out380, out _out381, out _out382);
                r = _out380;
                resultingOwnership = _out381;
                readIdents = _out382;
              }
            } else if (_source118.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2844___mcc_h227 = _source118.dtor_path;
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
              DAST._IType _2845___mcc_h230 = _source118.dtor_baseType;
              DAST._INewtypeRange _2846___mcc_h231 = _source118.dtor_range;
              bool _2847___mcc_h232 = _source118.dtor_erase;
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
          } else if (_source117.is_Nullable) {
            DAST._IType _2848___mcc_h239 = _source117.dtor_Nullable_a0;
            {
              RAST._IExpr _out389;
              DCOMP._IOwnership _out390;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out389, out _out390, out _out391);
              r = _out389;
              resultingOwnership = _out390;
              readIdents = _out391;
            }
          } else if (_source117.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2849___mcc_h242 = _source117.dtor_Tuple_a0;
            {
              RAST._IExpr _out392;
              DCOMP._IOwnership _out393;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out394;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out392, out _out393, out _out394);
              r = _out392;
              resultingOwnership = _out393;
              readIdents = _out394;
            }
          } else if (_source117.is_Array) {
            DAST._IType _2850___mcc_h245 = _source117.dtor_element;
            BigInteger _2851___mcc_h246 = _source117.dtor_dims;
            {
              RAST._IExpr _out395;
              DCOMP._IOwnership _out396;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out397;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out395, out _out396, out _out397);
              r = _out395;
              resultingOwnership = _out396;
              readIdents = _out397;
            }
          } else if (_source117.is_Seq) {
            DAST._IType _2852___mcc_h251 = _source117.dtor_element;
            {
              RAST._IExpr _out398;
              DCOMP._IOwnership _out399;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out398, out _out399, out _out400);
              r = _out398;
              resultingOwnership = _out399;
              readIdents = _out400;
            }
          } else if (_source117.is_Set) {
            DAST._IType _2853___mcc_h254 = _source117.dtor_element;
            {
              RAST._IExpr _out401;
              DCOMP._IOwnership _out402;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out401, out _out402, out _out403);
              r = _out401;
              resultingOwnership = _out402;
              readIdents = _out403;
            }
          } else if (_source117.is_Multiset) {
            DAST._IType _2854___mcc_h257 = _source117.dtor_element;
            {
              RAST._IExpr _out404;
              DCOMP._IOwnership _out405;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out404, out _out405, out _out406);
              r = _out404;
              resultingOwnership = _out405;
              readIdents = _out406;
            }
          } else if (_source117.is_Map) {
            DAST._IType _2855___mcc_h260 = _source117.dtor_key;
            DAST._IType _2856___mcc_h261 = _source117.dtor_value;
            {
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out407, out _out408, out _out409);
              r = _out407;
              resultingOwnership = _out408;
              readIdents = _out409;
            }
          } else if (_source117.is_SetBuilder) {
            DAST._IType _2857___mcc_h266 = _source117.dtor_element;
            {
              RAST._IExpr _out410;
              DCOMP._IOwnership _out411;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out410, out _out411, out _out412);
              r = _out410;
              resultingOwnership = _out411;
              readIdents = _out412;
            }
          } else if (_source117.is_MapBuilder) {
            DAST._IType _2858___mcc_h269 = _source117.dtor_key;
            DAST._IType _2859___mcc_h270 = _source117.dtor_value;
            {
              RAST._IExpr _out413;
              DCOMP._IOwnership _out414;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out413, out _out414, out _out415);
              r = _out413;
              resultingOwnership = _out414;
              readIdents = _out415;
            }
          } else if (_source117.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2860___mcc_h275 = _source117.dtor_args;
            DAST._IType _2861___mcc_h276 = _source117.dtor_result;
            {
              RAST._IExpr _out416;
              DCOMP._IOwnership _out417;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out418;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out416, out _out417, out _out418);
              r = _out416;
              resultingOwnership = _out417;
              readIdents = _out418;
            }
          } else if (_source117.is_Primitive) {
            DAST._IPrimitive _2862___mcc_h281 = _source117.dtor_Primitive_a0;
            {
              RAST._IExpr _out419;
              DCOMP._IOwnership _out420;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out419, out _out420, out _out421);
              r = _out419;
              resultingOwnership = _out420;
              readIdents = _out421;
            }
          } else if (_source117.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2863___mcc_h284 = _source117.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2864___mcc_h287 = _source117.dtor_TypeArg_a0;
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
        } else if (_source109.is_Tuple) {
          Dafny.ISequence<DAST._IType> _2865___mcc_h290 = _source109.dtor_Tuple_a0;
          DAST._IType _source119 = _2704___mcc_h1;
          if (_source119.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2866___mcc_h294 = _source119.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2867___mcc_h295 = _source119.dtor_typeArgs;
            DAST._IResolvedType _2868___mcc_h296 = _source119.dtor_resolved;
            DAST._IResolvedType _source120 = _2868___mcc_h296;
            if (_source120.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2869___mcc_h300 = _source120.dtor_path;
              {
                RAST._IExpr _out428;
                DCOMP._IOwnership _out429;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out428, out _out429, out _out430);
                r = _out428;
                resultingOwnership = _out429;
                readIdents = _out430;
              }
            } else if (_source120.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2870___mcc_h302 = _source120.dtor_path;
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
              DAST._IType _2871___mcc_h304 = _source120.dtor_baseType;
              DAST._INewtypeRange _2872___mcc_h305 = _source120.dtor_range;
              bool _2873___mcc_h306 = _source120.dtor_erase;
              bool _2874_erase = _2873___mcc_h306;
              DAST._INewtypeRange _2875_range = _2872___mcc_h305;
              DAST._IType _2876_b = _2871___mcc_h304;
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
          } else if (_source119.is_Nullable) {
            DAST._IType _2877___mcc_h310 = _source119.dtor_Nullable_a0;
            {
              RAST._IExpr _out437;
              DCOMP._IOwnership _out438;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out437, out _out438, out _out439);
              r = _out437;
              resultingOwnership = _out438;
              readIdents = _out439;
            }
          } else if (_source119.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2878___mcc_h312 = _source119.dtor_Tuple_a0;
            {
              RAST._IExpr _out440;
              DCOMP._IOwnership _out441;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out440, out _out441, out _out442);
              r = _out440;
              resultingOwnership = _out441;
              readIdents = _out442;
            }
          } else if (_source119.is_Array) {
            DAST._IType _2879___mcc_h314 = _source119.dtor_element;
            BigInteger _2880___mcc_h315 = _source119.dtor_dims;
            {
              RAST._IExpr _out443;
              DCOMP._IOwnership _out444;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out443, out _out444, out _out445);
              r = _out443;
              resultingOwnership = _out444;
              readIdents = _out445;
            }
          } else if (_source119.is_Seq) {
            DAST._IType _2881___mcc_h318 = _source119.dtor_element;
            {
              RAST._IExpr _out446;
              DCOMP._IOwnership _out447;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out446, out _out447, out _out448);
              r = _out446;
              resultingOwnership = _out447;
              readIdents = _out448;
            }
          } else if (_source119.is_Set) {
            DAST._IType _2882___mcc_h320 = _source119.dtor_element;
            {
              RAST._IExpr _out449;
              DCOMP._IOwnership _out450;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out449, out _out450, out _out451);
              r = _out449;
              resultingOwnership = _out450;
              readIdents = _out451;
            }
          } else if (_source119.is_Multiset) {
            DAST._IType _2883___mcc_h322 = _source119.dtor_element;
            {
              RAST._IExpr _out452;
              DCOMP._IOwnership _out453;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out452, out _out453, out _out454);
              r = _out452;
              resultingOwnership = _out453;
              readIdents = _out454;
            }
          } else if (_source119.is_Map) {
            DAST._IType _2884___mcc_h324 = _source119.dtor_key;
            DAST._IType _2885___mcc_h325 = _source119.dtor_value;
            {
              RAST._IExpr _out455;
              DCOMP._IOwnership _out456;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out455, out _out456, out _out457);
              r = _out455;
              resultingOwnership = _out456;
              readIdents = _out457;
            }
          } else if (_source119.is_SetBuilder) {
            DAST._IType _2886___mcc_h328 = _source119.dtor_element;
            {
              RAST._IExpr _out458;
              DCOMP._IOwnership _out459;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out458, out _out459, out _out460);
              r = _out458;
              resultingOwnership = _out459;
              readIdents = _out460;
            }
          } else if (_source119.is_MapBuilder) {
            DAST._IType _2887___mcc_h330 = _source119.dtor_key;
            DAST._IType _2888___mcc_h331 = _source119.dtor_value;
            {
              RAST._IExpr _out461;
              DCOMP._IOwnership _out462;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out463;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out461, out _out462, out _out463);
              r = _out461;
              resultingOwnership = _out462;
              readIdents = _out463;
            }
          } else if (_source119.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2889___mcc_h334 = _source119.dtor_args;
            DAST._IType _2890___mcc_h335 = _source119.dtor_result;
            {
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out464, out _out465, out _out466);
              r = _out464;
              resultingOwnership = _out465;
              readIdents = _out466;
            }
          } else if (_source119.is_Primitive) {
            DAST._IPrimitive _2891___mcc_h338 = _source119.dtor_Primitive_a0;
            {
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out467, out _out468, out _out469);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _out469;
            }
          } else if (_source119.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2892___mcc_h340 = _source119.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2893___mcc_h342 = _source119.dtor_TypeArg_a0;
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
        } else if (_source109.is_Array) {
          DAST._IType _2894___mcc_h344 = _source109.dtor_element;
          BigInteger _2895___mcc_h345 = _source109.dtor_dims;
          DAST._IType _source121 = _2704___mcc_h1;
          if (_source121.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2896___mcc_h352 = _source121.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2897___mcc_h353 = _source121.dtor_typeArgs;
            DAST._IResolvedType _2898___mcc_h354 = _source121.dtor_resolved;
            DAST._IResolvedType _source122 = _2898___mcc_h354;
            if (_source122.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2899___mcc_h358 = _source122.dtor_path;
              {
                RAST._IExpr _out476;
                DCOMP._IOwnership _out477;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out478;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out476, out _out477, out _out478);
                r = _out476;
                resultingOwnership = _out477;
                readIdents = _out478;
              }
            } else if (_source122.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2900___mcc_h360 = _source122.dtor_path;
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
              DAST._IType _2901___mcc_h362 = _source122.dtor_baseType;
              DAST._INewtypeRange _2902___mcc_h363 = _source122.dtor_range;
              bool _2903___mcc_h364 = _source122.dtor_erase;
              bool _2904_erase = _2903___mcc_h364;
              DAST._INewtypeRange _2905_range = _2902___mcc_h363;
              DAST._IType _2906_b = _2901___mcc_h362;
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
          } else if (_source121.is_Nullable) {
            DAST._IType _2907___mcc_h368 = _source121.dtor_Nullable_a0;
            {
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out485, out _out486, out _out487);
              r = _out485;
              resultingOwnership = _out486;
              readIdents = _out487;
            }
          } else if (_source121.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2908___mcc_h370 = _source121.dtor_Tuple_a0;
            {
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out488, out _out489, out _out490);
              r = _out488;
              resultingOwnership = _out489;
              readIdents = _out490;
            }
          } else if (_source121.is_Array) {
            DAST._IType _2909___mcc_h372 = _source121.dtor_element;
            BigInteger _2910___mcc_h373 = _source121.dtor_dims;
            {
              RAST._IExpr _out491;
              DCOMP._IOwnership _out492;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out491, out _out492, out _out493);
              r = _out491;
              resultingOwnership = _out492;
              readIdents = _out493;
            }
          } else if (_source121.is_Seq) {
            DAST._IType _2911___mcc_h376 = _source121.dtor_element;
            {
              RAST._IExpr _out494;
              DCOMP._IOwnership _out495;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out494, out _out495, out _out496);
              r = _out494;
              resultingOwnership = _out495;
              readIdents = _out496;
            }
          } else if (_source121.is_Set) {
            DAST._IType _2912___mcc_h378 = _source121.dtor_element;
            {
              RAST._IExpr _out497;
              DCOMP._IOwnership _out498;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out497, out _out498, out _out499);
              r = _out497;
              resultingOwnership = _out498;
              readIdents = _out499;
            }
          } else if (_source121.is_Multiset) {
            DAST._IType _2913___mcc_h380 = _source121.dtor_element;
            {
              RAST._IExpr _out500;
              DCOMP._IOwnership _out501;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out502;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out500, out _out501, out _out502);
              r = _out500;
              resultingOwnership = _out501;
              readIdents = _out502;
            }
          } else if (_source121.is_Map) {
            DAST._IType _2914___mcc_h382 = _source121.dtor_key;
            DAST._IType _2915___mcc_h383 = _source121.dtor_value;
            {
              RAST._IExpr _out503;
              DCOMP._IOwnership _out504;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out503, out _out504, out _out505);
              r = _out503;
              resultingOwnership = _out504;
              readIdents = _out505;
            }
          } else if (_source121.is_SetBuilder) {
            DAST._IType _2916___mcc_h386 = _source121.dtor_element;
            {
              RAST._IExpr _out506;
              DCOMP._IOwnership _out507;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out506, out _out507, out _out508);
              r = _out506;
              resultingOwnership = _out507;
              readIdents = _out508;
            }
          } else if (_source121.is_MapBuilder) {
            DAST._IType _2917___mcc_h388 = _source121.dtor_key;
            DAST._IType _2918___mcc_h389 = _source121.dtor_value;
            {
              RAST._IExpr _out509;
              DCOMP._IOwnership _out510;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out509, out _out510, out _out511);
              r = _out509;
              resultingOwnership = _out510;
              readIdents = _out511;
            }
          } else if (_source121.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2919___mcc_h392 = _source121.dtor_args;
            DAST._IType _2920___mcc_h393 = _source121.dtor_result;
            {
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out512, out _out513, out _out514);
              r = _out512;
              resultingOwnership = _out513;
              readIdents = _out514;
            }
          } else if (_source121.is_Primitive) {
            DAST._IPrimitive _2921___mcc_h396 = _source121.dtor_Primitive_a0;
            {
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out515, out _out516, out _out517);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _out517;
            }
          } else if (_source121.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2922___mcc_h398 = _source121.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2923___mcc_h400 = _source121.dtor_TypeArg_a0;
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
        } else if (_source109.is_Seq) {
          DAST._IType _2924___mcc_h402 = _source109.dtor_element;
          DAST._IType _source123 = _2704___mcc_h1;
          if (_source123.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2925___mcc_h406 = _source123.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2926___mcc_h407 = _source123.dtor_typeArgs;
            DAST._IResolvedType _2927___mcc_h408 = _source123.dtor_resolved;
            DAST._IResolvedType _source124 = _2927___mcc_h408;
            if (_source124.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2928___mcc_h412 = _source124.dtor_path;
              {
                RAST._IExpr _out524;
                DCOMP._IOwnership _out525;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out526;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out524, out _out525, out _out526);
                r = _out524;
                resultingOwnership = _out525;
                readIdents = _out526;
              }
            } else if (_source124.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2929___mcc_h414 = _source124.dtor_path;
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
              DAST._IType _2930___mcc_h416 = _source124.dtor_baseType;
              DAST._INewtypeRange _2931___mcc_h417 = _source124.dtor_range;
              bool _2932___mcc_h418 = _source124.dtor_erase;
              bool _2933_erase = _2932___mcc_h418;
              DAST._INewtypeRange _2934_range = _2931___mcc_h417;
              DAST._IType _2935_b = _2930___mcc_h416;
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
          } else if (_source123.is_Nullable) {
            DAST._IType _2936___mcc_h422 = _source123.dtor_Nullable_a0;
            {
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out533, out _out534, out _out535);
              r = _out533;
              resultingOwnership = _out534;
              readIdents = _out535;
            }
          } else if (_source123.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2937___mcc_h424 = _source123.dtor_Tuple_a0;
            {
              RAST._IExpr _out536;
              DCOMP._IOwnership _out537;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out536, out _out537, out _out538);
              r = _out536;
              resultingOwnership = _out537;
              readIdents = _out538;
            }
          } else if (_source123.is_Array) {
            DAST._IType _2938___mcc_h426 = _source123.dtor_element;
            BigInteger _2939___mcc_h427 = _source123.dtor_dims;
            {
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out539, out _out540, out _out541);
              r = _out539;
              resultingOwnership = _out540;
              readIdents = _out541;
            }
          } else if (_source123.is_Seq) {
            DAST._IType _2940___mcc_h430 = _source123.dtor_element;
            {
              RAST._IExpr _out542;
              DCOMP._IOwnership _out543;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out542, out _out543, out _out544);
              r = _out542;
              resultingOwnership = _out543;
              readIdents = _out544;
            }
          } else if (_source123.is_Set) {
            DAST._IType _2941___mcc_h432 = _source123.dtor_element;
            {
              RAST._IExpr _out545;
              DCOMP._IOwnership _out546;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out545, out _out546, out _out547);
              r = _out545;
              resultingOwnership = _out546;
              readIdents = _out547;
            }
          } else if (_source123.is_Multiset) {
            DAST._IType _2942___mcc_h434 = _source123.dtor_element;
            {
              RAST._IExpr _out548;
              DCOMP._IOwnership _out549;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out548, out _out549, out _out550);
              r = _out548;
              resultingOwnership = _out549;
              readIdents = _out550;
            }
          } else if (_source123.is_Map) {
            DAST._IType _2943___mcc_h436 = _source123.dtor_key;
            DAST._IType _2944___mcc_h437 = _source123.dtor_value;
            {
              RAST._IExpr _out551;
              DCOMP._IOwnership _out552;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out551, out _out552, out _out553);
              r = _out551;
              resultingOwnership = _out552;
              readIdents = _out553;
            }
          } else if (_source123.is_SetBuilder) {
            DAST._IType _2945___mcc_h440 = _source123.dtor_element;
            {
              RAST._IExpr _out554;
              DCOMP._IOwnership _out555;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out554, out _out555, out _out556);
              r = _out554;
              resultingOwnership = _out555;
              readIdents = _out556;
            }
          } else if (_source123.is_MapBuilder) {
            DAST._IType _2946___mcc_h442 = _source123.dtor_key;
            DAST._IType _2947___mcc_h443 = _source123.dtor_value;
            {
              RAST._IExpr _out557;
              DCOMP._IOwnership _out558;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out557, out _out558, out _out559);
              r = _out557;
              resultingOwnership = _out558;
              readIdents = _out559;
            }
          } else if (_source123.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2948___mcc_h446 = _source123.dtor_args;
            DAST._IType _2949___mcc_h447 = _source123.dtor_result;
            {
              RAST._IExpr _out560;
              DCOMP._IOwnership _out561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out560, out _out561, out _out562);
              r = _out560;
              resultingOwnership = _out561;
              readIdents = _out562;
            }
          } else if (_source123.is_Primitive) {
            DAST._IPrimitive _2950___mcc_h450 = _source123.dtor_Primitive_a0;
            {
              RAST._IExpr _out563;
              DCOMP._IOwnership _out564;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out563, out _out564, out _out565);
              r = _out563;
              resultingOwnership = _out564;
              readIdents = _out565;
            }
          } else if (_source123.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2951___mcc_h452 = _source123.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2952___mcc_h454 = _source123.dtor_TypeArg_a0;
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
        } else if (_source109.is_Set) {
          DAST._IType _2953___mcc_h456 = _source109.dtor_element;
          DAST._IType _source125 = _2704___mcc_h1;
          if (_source125.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2954___mcc_h460 = _source125.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2955___mcc_h461 = _source125.dtor_typeArgs;
            DAST._IResolvedType _2956___mcc_h462 = _source125.dtor_resolved;
            DAST._IResolvedType _source126 = _2956___mcc_h462;
            if (_source126.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2957___mcc_h466 = _source126.dtor_path;
              {
                RAST._IExpr _out572;
                DCOMP._IOwnership _out573;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out572, out _out573, out _out574);
                r = _out572;
                resultingOwnership = _out573;
                readIdents = _out574;
              }
            } else if (_source126.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2958___mcc_h468 = _source126.dtor_path;
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
              DAST._IType _2959___mcc_h470 = _source126.dtor_baseType;
              DAST._INewtypeRange _2960___mcc_h471 = _source126.dtor_range;
              bool _2961___mcc_h472 = _source126.dtor_erase;
              bool _2962_erase = _2961___mcc_h472;
              DAST._INewtypeRange _2963_range = _2960___mcc_h471;
              DAST._IType _2964_b = _2959___mcc_h470;
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
          } else if (_source125.is_Nullable) {
            DAST._IType _2965___mcc_h476 = _source125.dtor_Nullable_a0;
            {
              RAST._IExpr _out581;
              DCOMP._IOwnership _out582;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out583;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out581, out _out582, out _out583);
              r = _out581;
              resultingOwnership = _out582;
              readIdents = _out583;
            }
          } else if (_source125.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2966___mcc_h478 = _source125.dtor_Tuple_a0;
            {
              RAST._IExpr _out584;
              DCOMP._IOwnership _out585;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out584, out _out585, out _out586);
              r = _out584;
              resultingOwnership = _out585;
              readIdents = _out586;
            }
          } else if (_source125.is_Array) {
            DAST._IType _2967___mcc_h480 = _source125.dtor_element;
            BigInteger _2968___mcc_h481 = _source125.dtor_dims;
            {
              RAST._IExpr _out587;
              DCOMP._IOwnership _out588;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out587, out _out588, out _out589);
              r = _out587;
              resultingOwnership = _out588;
              readIdents = _out589;
            }
          } else if (_source125.is_Seq) {
            DAST._IType _2969___mcc_h484 = _source125.dtor_element;
            {
              RAST._IExpr _out590;
              DCOMP._IOwnership _out591;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out590, out _out591, out _out592);
              r = _out590;
              resultingOwnership = _out591;
              readIdents = _out592;
            }
          } else if (_source125.is_Set) {
            DAST._IType _2970___mcc_h486 = _source125.dtor_element;
            {
              RAST._IExpr _out593;
              DCOMP._IOwnership _out594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out595;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out593, out _out594, out _out595);
              r = _out593;
              resultingOwnership = _out594;
              readIdents = _out595;
            }
          } else if (_source125.is_Multiset) {
            DAST._IType _2971___mcc_h488 = _source125.dtor_element;
            {
              RAST._IExpr _out596;
              DCOMP._IOwnership _out597;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out596, out _out597, out _out598);
              r = _out596;
              resultingOwnership = _out597;
              readIdents = _out598;
            }
          } else if (_source125.is_Map) {
            DAST._IType _2972___mcc_h490 = _source125.dtor_key;
            DAST._IType _2973___mcc_h491 = _source125.dtor_value;
            {
              RAST._IExpr _out599;
              DCOMP._IOwnership _out600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out599, out _out600, out _out601);
              r = _out599;
              resultingOwnership = _out600;
              readIdents = _out601;
            }
          } else if (_source125.is_SetBuilder) {
            DAST._IType _2974___mcc_h494 = _source125.dtor_element;
            {
              RAST._IExpr _out602;
              DCOMP._IOwnership _out603;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out602, out _out603, out _out604);
              r = _out602;
              resultingOwnership = _out603;
              readIdents = _out604;
            }
          } else if (_source125.is_MapBuilder) {
            DAST._IType _2975___mcc_h496 = _source125.dtor_key;
            DAST._IType _2976___mcc_h497 = _source125.dtor_value;
            {
              RAST._IExpr _out605;
              DCOMP._IOwnership _out606;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out605, out _out606, out _out607);
              r = _out605;
              resultingOwnership = _out606;
              readIdents = _out607;
            }
          } else if (_source125.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2977___mcc_h500 = _source125.dtor_args;
            DAST._IType _2978___mcc_h501 = _source125.dtor_result;
            {
              RAST._IExpr _out608;
              DCOMP._IOwnership _out609;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out608, out _out609, out _out610);
              r = _out608;
              resultingOwnership = _out609;
              readIdents = _out610;
            }
          } else if (_source125.is_Primitive) {
            DAST._IPrimitive _2979___mcc_h504 = _source125.dtor_Primitive_a0;
            {
              RAST._IExpr _out611;
              DCOMP._IOwnership _out612;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out611, out _out612, out _out613);
              r = _out611;
              resultingOwnership = _out612;
              readIdents = _out613;
            }
          } else if (_source125.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2980___mcc_h506 = _source125.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2981___mcc_h508 = _source125.dtor_TypeArg_a0;
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
        } else if (_source109.is_Multiset) {
          DAST._IType _2982___mcc_h510 = _source109.dtor_element;
          DAST._IType _source127 = _2704___mcc_h1;
          if (_source127.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2983___mcc_h514 = _source127.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2984___mcc_h515 = _source127.dtor_typeArgs;
            DAST._IResolvedType _2985___mcc_h516 = _source127.dtor_resolved;
            DAST._IResolvedType _source128 = _2985___mcc_h516;
            if (_source128.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2986___mcc_h520 = _source128.dtor_path;
              {
                RAST._IExpr _out620;
                DCOMP._IOwnership _out621;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out620, out _out621, out _out622);
                r = _out620;
                resultingOwnership = _out621;
                readIdents = _out622;
              }
            } else if (_source128.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2987___mcc_h522 = _source128.dtor_path;
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
              DAST._IType _2988___mcc_h524 = _source128.dtor_baseType;
              DAST._INewtypeRange _2989___mcc_h525 = _source128.dtor_range;
              bool _2990___mcc_h526 = _source128.dtor_erase;
              bool _2991_erase = _2990___mcc_h526;
              DAST._INewtypeRange _2992_range = _2989___mcc_h525;
              DAST._IType _2993_b = _2988___mcc_h524;
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
          } else if (_source127.is_Nullable) {
            DAST._IType _2994___mcc_h530 = _source127.dtor_Nullable_a0;
            {
              RAST._IExpr _out629;
              DCOMP._IOwnership _out630;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out631;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out629, out _out630, out _out631);
              r = _out629;
              resultingOwnership = _out630;
              readIdents = _out631;
            }
          } else if (_source127.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2995___mcc_h532 = _source127.dtor_Tuple_a0;
            {
              RAST._IExpr _out632;
              DCOMP._IOwnership _out633;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out632, out _out633, out _out634);
              r = _out632;
              resultingOwnership = _out633;
              readIdents = _out634;
            }
          } else if (_source127.is_Array) {
            DAST._IType _2996___mcc_h534 = _source127.dtor_element;
            BigInteger _2997___mcc_h535 = _source127.dtor_dims;
            {
              RAST._IExpr _out635;
              DCOMP._IOwnership _out636;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out635, out _out636, out _out637);
              r = _out635;
              resultingOwnership = _out636;
              readIdents = _out637;
            }
          } else if (_source127.is_Seq) {
            DAST._IType _2998___mcc_h538 = _source127.dtor_element;
            {
              RAST._IExpr _out638;
              DCOMP._IOwnership _out639;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out638, out _out639, out _out640);
              r = _out638;
              resultingOwnership = _out639;
              readIdents = _out640;
            }
          } else if (_source127.is_Set) {
            DAST._IType _2999___mcc_h540 = _source127.dtor_element;
            {
              RAST._IExpr _out641;
              DCOMP._IOwnership _out642;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out641, out _out642, out _out643);
              r = _out641;
              resultingOwnership = _out642;
              readIdents = _out643;
            }
          } else if (_source127.is_Multiset) {
            DAST._IType _3000___mcc_h542 = _source127.dtor_element;
            {
              RAST._IExpr _out644;
              DCOMP._IOwnership _out645;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out646;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out644, out _out645, out _out646);
              r = _out644;
              resultingOwnership = _out645;
              readIdents = _out646;
            }
          } else if (_source127.is_Map) {
            DAST._IType _3001___mcc_h544 = _source127.dtor_key;
            DAST._IType _3002___mcc_h545 = _source127.dtor_value;
            {
              RAST._IExpr _out647;
              DCOMP._IOwnership _out648;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out647, out _out648, out _out649);
              r = _out647;
              resultingOwnership = _out648;
              readIdents = _out649;
            }
          } else if (_source127.is_SetBuilder) {
            DAST._IType _3003___mcc_h548 = _source127.dtor_element;
            {
              RAST._IExpr _out650;
              DCOMP._IOwnership _out651;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out652;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out650, out _out651, out _out652);
              r = _out650;
              resultingOwnership = _out651;
              readIdents = _out652;
            }
          } else if (_source127.is_MapBuilder) {
            DAST._IType _3004___mcc_h550 = _source127.dtor_key;
            DAST._IType _3005___mcc_h551 = _source127.dtor_value;
            {
              RAST._IExpr _out653;
              DCOMP._IOwnership _out654;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out653, out _out654, out _out655);
              r = _out653;
              resultingOwnership = _out654;
              readIdents = _out655;
            }
          } else if (_source127.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3006___mcc_h554 = _source127.dtor_args;
            DAST._IType _3007___mcc_h555 = _source127.dtor_result;
            {
              RAST._IExpr _out656;
              DCOMP._IOwnership _out657;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out656, out _out657, out _out658);
              r = _out656;
              resultingOwnership = _out657;
              readIdents = _out658;
            }
          } else if (_source127.is_Primitive) {
            DAST._IPrimitive _3008___mcc_h558 = _source127.dtor_Primitive_a0;
            {
              RAST._IExpr _out659;
              DCOMP._IOwnership _out660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out659, out _out660, out _out661);
              r = _out659;
              resultingOwnership = _out660;
              readIdents = _out661;
            }
          } else if (_source127.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3009___mcc_h560 = _source127.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _3010___mcc_h562 = _source127.dtor_TypeArg_a0;
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
        } else if (_source109.is_Map) {
          DAST._IType _3011___mcc_h564 = _source109.dtor_key;
          DAST._IType _3012___mcc_h565 = _source109.dtor_value;
          DAST._IType _source129 = _2704___mcc_h1;
          if (_source129.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3013___mcc_h572 = _source129.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _3014___mcc_h573 = _source129.dtor_typeArgs;
            DAST._IResolvedType _3015___mcc_h574 = _source129.dtor_resolved;
            DAST._IResolvedType _source130 = _3015___mcc_h574;
            if (_source130.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3016___mcc_h578 = _source130.dtor_path;
              {
                RAST._IExpr _out668;
                DCOMP._IOwnership _out669;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out670;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out668, out _out669, out _out670);
                r = _out668;
                resultingOwnership = _out669;
                readIdents = _out670;
              }
            } else if (_source130.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3017___mcc_h580 = _source130.dtor_path;
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
              DAST._IType _3018___mcc_h582 = _source130.dtor_baseType;
              DAST._INewtypeRange _3019___mcc_h583 = _source130.dtor_range;
              bool _3020___mcc_h584 = _source130.dtor_erase;
              bool _3021_erase = _3020___mcc_h584;
              DAST._INewtypeRange _3022_range = _3019___mcc_h583;
              DAST._IType _3023_b = _3018___mcc_h582;
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
          } else if (_source129.is_Nullable) {
            DAST._IType _3024___mcc_h588 = _source129.dtor_Nullable_a0;
            {
              RAST._IExpr _out677;
              DCOMP._IOwnership _out678;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out677, out _out678, out _out679);
              r = _out677;
              resultingOwnership = _out678;
              readIdents = _out679;
            }
          } else if (_source129.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3025___mcc_h590 = _source129.dtor_Tuple_a0;
            {
              RAST._IExpr _out680;
              DCOMP._IOwnership _out681;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out682;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out680, out _out681, out _out682);
              r = _out680;
              resultingOwnership = _out681;
              readIdents = _out682;
            }
          } else if (_source129.is_Array) {
            DAST._IType _3026___mcc_h592 = _source129.dtor_element;
            BigInteger _3027___mcc_h593 = _source129.dtor_dims;
            {
              RAST._IExpr _out683;
              DCOMP._IOwnership _out684;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out685;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out683, out _out684, out _out685);
              r = _out683;
              resultingOwnership = _out684;
              readIdents = _out685;
            }
          } else if (_source129.is_Seq) {
            DAST._IType _3028___mcc_h596 = _source129.dtor_element;
            {
              RAST._IExpr _out686;
              DCOMP._IOwnership _out687;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out688;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out686, out _out687, out _out688);
              r = _out686;
              resultingOwnership = _out687;
              readIdents = _out688;
            }
          } else if (_source129.is_Set) {
            DAST._IType _3029___mcc_h598 = _source129.dtor_element;
            {
              RAST._IExpr _out689;
              DCOMP._IOwnership _out690;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out689, out _out690, out _out691);
              r = _out689;
              resultingOwnership = _out690;
              readIdents = _out691;
            }
          } else if (_source129.is_Multiset) {
            DAST._IType _3030___mcc_h600 = _source129.dtor_element;
            {
              RAST._IExpr _out692;
              DCOMP._IOwnership _out693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out694;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out692, out _out693, out _out694);
              r = _out692;
              resultingOwnership = _out693;
              readIdents = _out694;
            }
          } else if (_source129.is_Map) {
            DAST._IType _3031___mcc_h602 = _source129.dtor_key;
            DAST._IType _3032___mcc_h603 = _source129.dtor_value;
            {
              RAST._IExpr _out695;
              DCOMP._IOwnership _out696;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out697;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out695, out _out696, out _out697);
              r = _out695;
              resultingOwnership = _out696;
              readIdents = _out697;
            }
          } else if (_source129.is_SetBuilder) {
            DAST._IType _3033___mcc_h606 = _source129.dtor_element;
            {
              RAST._IExpr _out698;
              DCOMP._IOwnership _out699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out698, out _out699, out _out700);
              r = _out698;
              resultingOwnership = _out699;
              readIdents = _out700;
            }
          } else if (_source129.is_MapBuilder) {
            DAST._IType _3034___mcc_h608 = _source129.dtor_key;
            DAST._IType _3035___mcc_h609 = _source129.dtor_value;
            {
              RAST._IExpr _out701;
              DCOMP._IOwnership _out702;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out703;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out701, out _out702, out _out703);
              r = _out701;
              resultingOwnership = _out702;
              readIdents = _out703;
            }
          } else if (_source129.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3036___mcc_h612 = _source129.dtor_args;
            DAST._IType _3037___mcc_h613 = _source129.dtor_result;
            {
              RAST._IExpr _out704;
              DCOMP._IOwnership _out705;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out706;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out704, out _out705, out _out706);
              r = _out704;
              resultingOwnership = _out705;
              readIdents = _out706;
            }
          } else if (_source129.is_Primitive) {
            DAST._IPrimitive _3038___mcc_h616 = _source129.dtor_Primitive_a0;
            {
              RAST._IExpr _out707;
              DCOMP._IOwnership _out708;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out709;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out707, out _out708, out _out709);
              r = _out707;
              resultingOwnership = _out708;
              readIdents = _out709;
            }
          } else if (_source129.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3039___mcc_h618 = _source129.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _3040___mcc_h620 = _source129.dtor_TypeArg_a0;
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
        } else if (_source109.is_SetBuilder) {
          DAST._IType _3041___mcc_h622 = _source109.dtor_element;
          DAST._IType _source131 = _2704___mcc_h1;
          if (_source131.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3042___mcc_h626 = _source131.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _3043___mcc_h627 = _source131.dtor_typeArgs;
            DAST._IResolvedType _3044___mcc_h628 = _source131.dtor_resolved;
            DAST._IResolvedType _source132 = _3044___mcc_h628;
            if (_source132.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3045___mcc_h632 = _source132.dtor_path;
              {
                RAST._IExpr _out716;
                DCOMP._IOwnership _out717;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out718;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out716, out _out717, out _out718);
                r = _out716;
                resultingOwnership = _out717;
                readIdents = _out718;
              }
            } else if (_source132.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3046___mcc_h634 = _source132.dtor_path;
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
              DAST._IType _3047___mcc_h636 = _source132.dtor_baseType;
              DAST._INewtypeRange _3048___mcc_h637 = _source132.dtor_range;
              bool _3049___mcc_h638 = _source132.dtor_erase;
              bool _3050_erase = _3049___mcc_h638;
              DAST._INewtypeRange _3051_range = _3048___mcc_h637;
              DAST._IType _3052_b = _3047___mcc_h636;
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
          } else if (_source131.is_Nullable) {
            DAST._IType _3053___mcc_h642 = _source131.dtor_Nullable_a0;
            {
              RAST._IExpr _out725;
              DCOMP._IOwnership _out726;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out727;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out725, out _out726, out _out727);
              r = _out725;
              resultingOwnership = _out726;
              readIdents = _out727;
            }
          } else if (_source131.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3054___mcc_h644 = _source131.dtor_Tuple_a0;
            {
              RAST._IExpr _out728;
              DCOMP._IOwnership _out729;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out730;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out728, out _out729, out _out730);
              r = _out728;
              resultingOwnership = _out729;
              readIdents = _out730;
            }
          } else if (_source131.is_Array) {
            DAST._IType _3055___mcc_h646 = _source131.dtor_element;
            BigInteger _3056___mcc_h647 = _source131.dtor_dims;
            {
              RAST._IExpr _out731;
              DCOMP._IOwnership _out732;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out733;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out731, out _out732, out _out733);
              r = _out731;
              resultingOwnership = _out732;
              readIdents = _out733;
            }
          } else if (_source131.is_Seq) {
            DAST._IType _3057___mcc_h650 = _source131.dtor_element;
            {
              RAST._IExpr _out734;
              DCOMP._IOwnership _out735;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out734, out _out735, out _out736);
              r = _out734;
              resultingOwnership = _out735;
              readIdents = _out736;
            }
          } else if (_source131.is_Set) {
            DAST._IType _3058___mcc_h652 = _source131.dtor_element;
            {
              RAST._IExpr _out737;
              DCOMP._IOwnership _out738;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out739;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out737, out _out738, out _out739);
              r = _out737;
              resultingOwnership = _out738;
              readIdents = _out739;
            }
          } else if (_source131.is_Multiset) {
            DAST._IType _3059___mcc_h654 = _source131.dtor_element;
            {
              RAST._IExpr _out740;
              DCOMP._IOwnership _out741;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out742;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out740, out _out741, out _out742);
              r = _out740;
              resultingOwnership = _out741;
              readIdents = _out742;
            }
          } else if (_source131.is_Map) {
            DAST._IType _3060___mcc_h656 = _source131.dtor_key;
            DAST._IType _3061___mcc_h657 = _source131.dtor_value;
            {
              RAST._IExpr _out743;
              DCOMP._IOwnership _out744;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out745;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out743, out _out744, out _out745);
              r = _out743;
              resultingOwnership = _out744;
              readIdents = _out745;
            }
          } else if (_source131.is_SetBuilder) {
            DAST._IType _3062___mcc_h660 = _source131.dtor_element;
            {
              RAST._IExpr _out746;
              DCOMP._IOwnership _out747;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out746, out _out747, out _out748);
              r = _out746;
              resultingOwnership = _out747;
              readIdents = _out748;
            }
          } else if (_source131.is_MapBuilder) {
            DAST._IType _3063___mcc_h662 = _source131.dtor_key;
            DAST._IType _3064___mcc_h663 = _source131.dtor_value;
            {
              RAST._IExpr _out749;
              DCOMP._IOwnership _out750;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out751;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out749, out _out750, out _out751);
              r = _out749;
              resultingOwnership = _out750;
              readIdents = _out751;
            }
          } else if (_source131.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3065___mcc_h666 = _source131.dtor_args;
            DAST._IType _3066___mcc_h667 = _source131.dtor_result;
            {
              RAST._IExpr _out752;
              DCOMP._IOwnership _out753;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out754;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out752, out _out753, out _out754);
              r = _out752;
              resultingOwnership = _out753;
              readIdents = _out754;
            }
          } else if (_source131.is_Primitive) {
            DAST._IPrimitive _3067___mcc_h670 = _source131.dtor_Primitive_a0;
            {
              RAST._IExpr _out755;
              DCOMP._IOwnership _out756;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out757;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out755, out _out756, out _out757);
              r = _out755;
              resultingOwnership = _out756;
              readIdents = _out757;
            }
          } else if (_source131.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3068___mcc_h672 = _source131.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _3069___mcc_h674 = _source131.dtor_TypeArg_a0;
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
        } else if (_source109.is_MapBuilder) {
          DAST._IType _3070___mcc_h676 = _source109.dtor_key;
          DAST._IType _3071___mcc_h677 = _source109.dtor_value;
          DAST._IType _source133 = _2704___mcc_h1;
          if (_source133.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3072___mcc_h684 = _source133.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _3073___mcc_h685 = _source133.dtor_typeArgs;
            DAST._IResolvedType _3074___mcc_h686 = _source133.dtor_resolved;
            DAST._IResolvedType _source134 = _3074___mcc_h686;
            if (_source134.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3075___mcc_h690 = _source134.dtor_path;
              {
                RAST._IExpr _out764;
                DCOMP._IOwnership _out765;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out766;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out764, out _out765, out _out766);
                r = _out764;
                resultingOwnership = _out765;
                readIdents = _out766;
              }
            } else if (_source134.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3076___mcc_h692 = _source134.dtor_path;
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
              DAST._IType _3077___mcc_h694 = _source134.dtor_baseType;
              DAST._INewtypeRange _3078___mcc_h695 = _source134.dtor_range;
              bool _3079___mcc_h696 = _source134.dtor_erase;
              bool _3080_erase = _3079___mcc_h696;
              DAST._INewtypeRange _3081_range = _3078___mcc_h695;
              DAST._IType _3082_b = _3077___mcc_h694;
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
          } else if (_source133.is_Nullable) {
            DAST._IType _3083___mcc_h700 = _source133.dtor_Nullable_a0;
            {
              RAST._IExpr _out773;
              DCOMP._IOwnership _out774;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out775;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out773, out _out774, out _out775);
              r = _out773;
              resultingOwnership = _out774;
              readIdents = _out775;
            }
          } else if (_source133.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3084___mcc_h702 = _source133.dtor_Tuple_a0;
            {
              RAST._IExpr _out776;
              DCOMP._IOwnership _out777;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out778;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out776, out _out777, out _out778);
              r = _out776;
              resultingOwnership = _out777;
              readIdents = _out778;
            }
          } else if (_source133.is_Array) {
            DAST._IType _3085___mcc_h704 = _source133.dtor_element;
            BigInteger _3086___mcc_h705 = _source133.dtor_dims;
            {
              RAST._IExpr _out779;
              DCOMP._IOwnership _out780;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out779, out _out780, out _out781);
              r = _out779;
              resultingOwnership = _out780;
              readIdents = _out781;
            }
          } else if (_source133.is_Seq) {
            DAST._IType _3087___mcc_h708 = _source133.dtor_element;
            {
              RAST._IExpr _out782;
              DCOMP._IOwnership _out783;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out784;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out782, out _out783, out _out784);
              r = _out782;
              resultingOwnership = _out783;
              readIdents = _out784;
            }
          } else if (_source133.is_Set) {
            DAST._IType _3088___mcc_h710 = _source133.dtor_element;
            {
              RAST._IExpr _out785;
              DCOMP._IOwnership _out786;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out787;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out785, out _out786, out _out787);
              r = _out785;
              resultingOwnership = _out786;
              readIdents = _out787;
            }
          } else if (_source133.is_Multiset) {
            DAST._IType _3089___mcc_h712 = _source133.dtor_element;
            {
              RAST._IExpr _out788;
              DCOMP._IOwnership _out789;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out790;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out788, out _out789, out _out790);
              r = _out788;
              resultingOwnership = _out789;
              readIdents = _out790;
            }
          } else if (_source133.is_Map) {
            DAST._IType _3090___mcc_h714 = _source133.dtor_key;
            DAST._IType _3091___mcc_h715 = _source133.dtor_value;
            {
              RAST._IExpr _out791;
              DCOMP._IOwnership _out792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out791, out _out792, out _out793);
              r = _out791;
              resultingOwnership = _out792;
              readIdents = _out793;
            }
          } else if (_source133.is_SetBuilder) {
            DAST._IType _3092___mcc_h718 = _source133.dtor_element;
            {
              RAST._IExpr _out794;
              DCOMP._IOwnership _out795;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out796;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out794, out _out795, out _out796);
              r = _out794;
              resultingOwnership = _out795;
              readIdents = _out796;
            }
          } else if (_source133.is_MapBuilder) {
            DAST._IType _3093___mcc_h720 = _source133.dtor_key;
            DAST._IType _3094___mcc_h721 = _source133.dtor_value;
            {
              RAST._IExpr _out797;
              DCOMP._IOwnership _out798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out799;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out797, out _out798, out _out799);
              r = _out797;
              resultingOwnership = _out798;
              readIdents = _out799;
            }
          } else if (_source133.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3095___mcc_h724 = _source133.dtor_args;
            DAST._IType _3096___mcc_h725 = _source133.dtor_result;
            {
              RAST._IExpr _out800;
              DCOMP._IOwnership _out801;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out802;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out800, out _out801, out _out802);
              r = _out800;
              resultingOwnership = _out801;
              readIdents = _out802;
            }
          } else if (_source133.is_Primitive) {
            DAST._IPrimitive _3097___mcc_h728 = _source133.dtor_Primitive_a0;
            {
              RAST._IExpr _out803;
              DCOMP._IOwnership _out804;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out803, out _out804, out _out805);
              r = _out803;
              resultingOwnership = _out804;
              readIdents = _out805;
            }
          } else if (_source133.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3098___mcc_h730 = _source133.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _3099___mcc_h732 = _source133.dtor_TypeArg_a0;
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
        } else if (_source109.is_Arrow) {
          Dafny.ISequence<DAST._IType> _3100___mcc_h734 = _source109.dtor_args;
          DAST._IType _3101___mcc_h735 = _source109.dtor_result;
          DAST._IType _source135 = _2704___mcc_h1;
          if (_source135.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3102___mcc_h742 = _source135.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _3103___mcc_h743 = _source135.dtor_typeArgs;
            DAST._IResolvedType _3104___mcc_h744 = _source135.dtor_resolved;
            DAST._IResolvedType _source136 = _3104___mcc_h744;
            if (_source136.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3105___mcc_h748 = _source136.dtor_path;
              {
                RAST._IExpr _out812;
                DCOMP._IOwnership _out813;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out814;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out812, out _out813, out _out814);
                r = _out812;
                resultingOwnership = _out813;
                readIdents = _out814;
              }
            } else if (_source136.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3106___mcc_h750 = _source136.dtor_path;
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
              DAST._IType _3107___mcc_h752 = _source136.dtor_baseType;
              DAST._INewtypeRange _3108___mcc_h753 = _source136.dtor_range;
              bool _3109___mcc_h754 = _source136.dtor_erase;
              bool _3110_erase = _3109___mcc_h754;
              DAST._INewtypeRange _3111_range = _3108___mcc_h753;
              DAST._IType _3112_b = _3107___mcc_h752;
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
          } else if (_source135.is_Nullable) {
            DAST._IType _3113___mcc_h758 = _source135.dtor_Nullable_a0;
            {
              RAST._IExpr _out821;
              DCOMP._IOwnership _out822;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out823;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out821, out _out822, out _out823);
              r = _out821;
              resultingOwnership = _out822;
              readIdents = _out823;
            }
          } else if (_source135.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3114___mcc_h760 = _source135.dtor_Tuple_a0;
            {
              RAST._IExpr _out824;
              DCOMP._IOwnership _out825;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out824, out _out825, out _out826);
              r = _out824;
              resultingOwnership = _out825;
              readIdents = _out826;
            }
          } else if (_source135.is_Array) {
            DAST._IType _3115___mcc_h762 = _source135.dtor_element;
            BigInteger _3116___mcc_h763 = _source135.dtor_dims;
            {
              RAST._IExpr _out827;
              DCOMP._IOwnership _out828;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out829;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out827, out _out828, out _out829);
              r = _out827;
              resultingOwnership = _out828;
              readIdents = _out829;
            }
          } else if (_source135.is_Seq) {
            DAST._IType _3117___mcc_h766 = _source135.dtor_element;
            {
              RAST._IExpr _out830;
              DCOMP._IOwnership _out831;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out832;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out830, out _out831, out _out832);
              r = _out830;
              resultingOwnership = _out831;
              readIdents = _out832;
            }
          } else if (_source135.is_Set) {
            DAST._IType _3118___mcc_h768 = _source135.dtor_element;
            {
              RAST._IExpr _out833;
              DCOMP._IOwnership _out834;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out835;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out833, out _out834, out _out835);
              r = _out833;
              resultingOwnership = _out834;
              readIdents = _out835;
            }
          } else if (_source135.is_Multiset) {
            DAST._IType _3119___mcc_h770 = _source135.dtor_element;
            {
              RAST._IExpr _out836;
              DCOMP._IOwnership _out837;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out836, out _out837, out _out838);
              r = _out836;
              resultingOwnership = _out837;
              readIdents = _out838;
            }
          } else if (_source135.is_Map) {
            DAST._IType _3120___mcc_h772 = _source135.dtor_key;
            DAST._IType _3121___mcc_h773 = _source135.dtor_value;
            {
              RAST._IExpr _out839;
              DCOMP._IOwnership _out840;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out841;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out839, out _out840, out _out841);
              r = _out839;
              resultingOwnership = _out840;
              readIdents = _out841;
            }
          } else if (_source135.is_SetBuilder) {
            DAST._IType _3122___mcc_h776 = _source135.dtor_element;
            {
              RAST._IExpr _out842;
              DCOMP._IOwnership _out843;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out844;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out842, out _out843, out _out844);
              r = _out842;
              resultingOwnership = _out843;
              readIdents = _out844;
            }
          } else if (_source135.is_MapBuilder) {
            DAST._IType _3123___mcc_h778 = _source135.dtor_key;
            DAST._IType _3124___mcc_h779 = _source135.dtor_value;
            {
              RAST._IExpr _out845;
              DCOMP._IOwnership _out846;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out847;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out845, out _out846, out _out847);
              r = _out845;
              resultingOwnership = _out846;
              readIdents = _out847;
            }
          } else if (_source135.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3125___mcc_h782 = _source135.dtor_args;
            DAST._IType _3126___mcc_h783 = _source135.dtor_result;
            {
              RAST._IExpr _out848;
              DCOMP._IOwnership _out849;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out848, out _out849, out _out850);
              r = _out848;
              resultingOwnership = _out849;
              readIdents = _out850;
            }
          } else if (_source135.is_Primitive) {
            DAST._IPrimitive _3127___mcc_h786 = _source135.dtor_Primitive_a0;
            {
              RAST._IExpr _out851;
              DCOMP._IOwnership _out852;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out853;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out851, out _out852, out _out853);
              r = _out851;
              resultingOwnership = _out852;
              readIdents = _out853;
            }
          } else if (_source135.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3128___mcc_h788 = _source135.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _3129___mcc_h790 = _source135.dtor_TypeArg_a0;
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
        } else if (_source109.is_Primitive) {
          DAST._IPrimitive _3130___mcc_h792 = _source109.dtor_Primitive_a0;
          DAST._IPrimitive _source137 = _3130___mcc_h792;
          if (_source137.is_Int) {
            DAST._IType _source138 = _2704___mcc_h1;
            if (_source138.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3131___mcc_h796 = _source138.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _3132___mcc_h797 = _source138.dtor_typeArgs;
              DAST._IResolvedType _3133___mcc_h798 = _source138.dtor_resolved;
              DAST._IResolvedType _source139 = _3133___mcc_h798;
              if (_source139.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3134___mcc_h802 = _source139.dtor_path;
                {
                  RAST._IExpr _out860;
                  DCOMP._IOwnership _out861;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out860, out _out861, out _out862);
                  r = _out860;
                  resultingOwnership = _out861;
                  readIdents = _out862;
                }
              } else if (_source139.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3135___mcc_h804 = _source139.dtor_path;
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
                DAST._IType _3136___mcc_h806 = _source139.dtor_baseType;
                DAST._INewtypeRange _3137___mcc_h807 = _source139.dtor_range;
                bool _3138___mcc_h808 = _source139.dtor_erase;
                bool _3139_erase = _3138___mcc_h808;
                DAST._INewtypeRange _3140_range = _3137___mcc_h807;
                DAST._IType _3141_b = _3136___mcc_h806;
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
            } else if (_source138.is_Nullable) {
              DAST._IType _3142___mcc_h812 = _source138.dtor_Nullable_a0;
              {
                RAST._IExpr _out869;
                DCOMP._IOwnership _out870;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out871;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out869, out _out870, out _out871);
                r = _out869;
                resultingOwnership = _out870;
                readIdents = _out871;
              }
            } else if (_source138.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3143___mcc_h814 = _source138.dtor_Tuple_a0;
              {
                RAST._IExpr _out872;
                DCOMP._IOwnership _out873;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out872, out _out873, out _out874);
                r = _out872;
                resultingOwnership = _out873;
                readIdents = _out874;
              }
            } else if (_source138.is_Array) {
              DAST._IType _3144___mcc_h816 = _source138.dtor_element;
              BigInteger _3145___mcc_h817 = _source138.dtor_dims;
              {
                RAST._IExpr _out875;
                DCOMP._IOwnership _out876;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out877;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out875, out _out876, out _out877);
                r = _out875;
                resultingOwnership = _out876;
                readIdents = _out877;
              }
            } else if (_source138.is_Seq) {
              DAST._IType _3146___mcc_h820 = _source138.dtor_element;
              {
                RAST._IExpr _out878;
                DCOMP._IOwnership _out879;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out880;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out878, out _out879, out _out880);
                r = _out878;
                resultingOwnership = _out879;
                readIdents = _out880;
              }
            } else if (_source138.is_Set) {
              DAST._IType _3147___mcc_h822 = _source138.dtor_element;
              {
                RAST._IExpr _out881;
                DCOMP._IOwnership _out882;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out881, out _out882, out _out883);
                r = _out881;
                resultingOwnership = _out882;
                readIdents = _out883;
              }
            } else if (_source138.is_Multiset) {
              DAST._IType _3148___mcc_h824 = _source138.dtor_element;
              {
                RAST._IExpr _out884;
                DCOMP._IOwnership _out885;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out886;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out884, out _out885, out _out886);
                r = _out884;
                resultingOwnership = _out885;
                readIdents = _out886;
              }
            } else if (_source138.is_Map) {
              DAST._IType _3149___mcc_h826 = _source138.dtor_key;
              DAST._IType _3150___mcc_h827 = _source138.dtor_value;
              {
                RAST._IExpr _out887;
                DCOMP._IOwnership _out888;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out889;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out887, out _out888, out _out889);
                r = _out887;
                resultingOwnership = _out888;
                readIdents = _out889;
              }
            } else if (_source138.is_SetBuilder) {
              DAST._IType _3151___mcc_h830 = _source138.dtor_element;
              {
                RAST._IExpr _out890;
                DCOMP._IOwnership _out891;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out892;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out890, out _out891, out _out892);
                r = _out890;
                resultingOwnership = _out891;
                readIdents = _out892;
              }
            } else if (_source138.is_MapBuilder) {
              DAST._IType _3152___mcc_h832 = _source138.dtor_key;
              DAST._IType _3153___mcc_h833 = _source138.dtor_value;
              {
                RAST._IExpr _out893;
                DCOMP._IOwnership _out894;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out893, out _out894, out _out895);
                r = _out893;
                resultingOwnership = _out894;
                readIdents = _out895;
              }
            } else if (_source138.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3154___mcc_h836 = _source138.dtor_args;
              DAST._IType _3155___mcc_h837 = _source138.dtor_result;
              {
                RAST._IExpr _out896;
                DCOMP._IOwnership _out897;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out898;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out896, out _out897, out _out898);
                r = _out896;
                resultingOwnership = _out897;
                readIdents = _out898;
              }
            } else if (_source138.is_Primitive) {
              DAST._IPrimitive _3156___mcc_h840 = _source138.dtor_Primitive_a0;
              DAST._IPrimitive _source140 = _3156___mcc_h840;
              if (_source140.is_Int) {
                {
                  RAST._IExpr _out899;
                  DCOMP._IOwnership _out900;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out901;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out899, out _out900, out _out901);
                  r = _out899;
                  resultingOwnership = _out900;
                  readIdents = _out901;
                }
              } else if (_source140.is_Real) {
                {
                  RAST._IExpr _3157_recursiveGen;
                  DCOMP._IOwnership _3158___v74;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3159_recIdents;
                  RAST._IExpr _out902;
                  DCOMP._IOwnership _out903;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out904;
                  (this).GenExpr(_2697_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out902, out _out903, out _out904);
                  _3157_recursiveGen = _out902;
                  _3158___v74 = _out903;
                  _3159_recIdents = _out904;
                  r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_3157_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                  RAST._IExpr _out905;
                  DCOMP._IOwnership _out906;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out905, out _out906);
                  r = _out905;
                  resultingOwnership = _out906;
                  readIdents = _3159_recIdents;
                }
              } else if (_source140.is_String) {
                {
                  RAST._IExpr _out907;
                  DCOMP._IOwnership _out908;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out909;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out907, out _out908, out _out909);
                  r = _out907;
                  resultingOwnership = _out908;
                  readIdents = _out909;
                }
              } else if (_source140.is_Bool) {
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
                  RAST._IType _3160_rhsType;
                  RAST._IType _out913;
                  _out913 = (this).GenType(_2699_toTpe, true, false);
                  _3160_rhsType = _out913;
                  RAST._IExpr _3161_recursiveGen;
                  DCOMP._IOwnership _3162___v80;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3163_recIdents;
                  RAST._IExpr _out914;
                  DCOMP._IOwnership _out915;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out916;
                  (this).GenExpr(_2697_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out914, out _out915, out _out916);
                  _3161_recursiveGen = _out914;
                  _3162___v80 = _out915;
                  _3163_recIdents = _out916;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_3161_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                  RAST._IExpr _out917;
                  DCOMP._IOwnership _out918;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out917, out _out918);
                  r = _out917;
                  resultingOwnership = _out918;
                  readIdents = _3163_recIdents;
                }
              }
            } else if (_source138.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3164___mcc_h842 = _source138.dtor_Passthrough_a0;
              {
                RAST._IType _3165_rhsType;
                RAST._IType _out919;
                _out919 = (this).GenType(_2699_toTpe, true, false);
                _3165_rhsType = _out919;
                RAST._IExpr _3166_recursiveGen;
                DCOMP._IOwnership _3167___v77;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3168_recIdents;
                RAST._IExpr _out920;
                DCOMP._IOwnership _out921;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out922;
                (this).GenExpr(_2697_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out920, out _out921, out _out922);
                _3166_recursiveGen = _out920;
                _3167___v77 = _out921;
                _3168_recIdents = _out922;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3165_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_3166_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                RAST._IExpr _out923;
                DCOMP._IOwnership _out924;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out923, out _out924);
                r = _out923;
                resultingOwnership = _out924;
                readIdents = _3168_recIdents;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3169___mcc_h844 = _source138.dtor_TypeArg_a0;
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
          } else if (_source137.is_Real) {
            DAST._IType _source141 = _2704___mcc_h1;
            if (_source141.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3170___mcc_h846 = _source141.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _3171___mcc_h847 = _source141.dtor_typeArgs;
              DAST._IResolvedType _3172___mcc_h848 = _source141.dtor_resolved;
              DAST._IResolvedType _source142 = _3172___mcc_h848;
              if (_source142.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3173___mcc_h852 = _source142.dtor_path;
                {
                  RAST._IExpr _out928;
                  DCOMP._IOwnership _out929;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out930;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out928, out _out929, out _out930);
                  r = _out928;
                  resultingOwnership = _out929;
                  readIdents = _out930;
                }
              } else if (_source142.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3174___mcc_h854 = _source142.dtor_path;
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
                DAST._IType _3175___mcc_h856 = _source142.dtor_baseType;
                DAST._INewtypeRange _3176___mcc_h857 = _source142.dtor_range;
                bool _3177___mcc_h858 = _source142.dtor_erase;
                bool _3178_erase = _3177___mcc_h858;
                DAST._INewtypeRange _3179_range = _3176___mcc_h857;
                DAST._IType _3180_b = _3175___mcc_h856;
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
            } else if (_source141.is_Nullable) {
              DAST._IType _3181___mcc_h862 = _source141.dtor_Nullable_a0;
              {
                RAST._IExpr _out937;
                DCOMP._IOwnership _out938;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out939;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out937, out _out938, out _out939);
                r = _out937;
                resultingOwnership = _out938;
                readIdents = _out939;
              }
            } else if (_source141.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3182___mcc_h864 = _source141.dtor_Tuple_a0;
              {
                RAST._IExpr _out940;
                DCOMP._IOwnership _out941;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out942;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out940, out _out941, out _out942);
                r = _out940;
                resultingOwnership = _out941;
                readIdents = _out942;
              }
            } else if (_source141.is_Array) {
              DAST._IType _3183___mcc_h866 = _source141.dtor_element;
              BigInteger _3184___mcc_h867 = _source141.dtor_dims;
              {
                RAST._IExpr _out943;
                DCOMP._IOwnership _out944;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out945;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out943, out _out944, out _out945);
                r = _out943;
                resultingOwnership = _out944;
                readIdents = _out945;
              }
            } else if (_source141.is_Seq) {
              DAST._IType _3185___mcc_h870 = _source141.dtor_element;
              {
                RAST._IExpr _out946;
                DCOMP._IOwnership _out947;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out948;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out946, out _out947, out _out948);
                r = _out946;
                resultingOwnership = _out947;
                readIdents = _out948;
              }
            } else if (_source141.is_Set) {
              DAST._IType _3186___mcc_h872 = _source141.dtor_element;
              {
                RAST._IExpr _out949;
                DCOMP._IOwnership _out950;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out951;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out949, out _out950, out _out951);
                r = _out949;
                resultingOwnership = _out950;
                readIdents = _out951;
              }
            } else if (_source141.is_Multiset) {
              DAST._IType _3187___mcc_h874 = _source141.dtor_element;
              {
                RAST._IExpr _out952;
                DCOMP._IOwnership _out953;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out954;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out952, out _out953, out _out954);
                r = _out952;
                resultingOwnership = _out953;
                readIdents = _out954;
              }
            } else if (_source141.is_Map) {
              DAST._IType _3188___mcc_h876 = _source141.dtor_key;
              DAST._IType _3189___mcc_h877 = _source141.dtor_value;
              {
                RAST._IExpr _out955;
                DCOMP._IOwnership _out956;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out957;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out955, out _out956, out _out957);
                r = _out955;
                resultingOwnership = _out956;
                readIdents = _out957;
              }
            } else if (_source141.is_SetBuilder) {
              DAST._IType _3190___mcc_h880 = _source141.dtor_element;
              {
                RAST._IExpr _out958;
                DCOMP._IOwnership _out959;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out960;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out958, out _out959, out _out960);
                r = _out958;
                resultingOwnership = _out959;
                readIdents = _out960;
              }
            } else if (_source141.is_MapBuilder) {
              DAST._IType _3191___mcc_h882 = _source141.dtor_key;
              DAST._IType _3192___mcc_h883 = _source141.dtor_value;
              {
                RAST._IExpr _out961;
                DCOMP._IOwnership _out962;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out963;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out961, out _out962, out _out963);
                r = _out961;
                resultingOwnership = _out962;
                readIdents = _out963;
              }
            } else if (_source141.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3193___mcc_h886 = _source141.dtor_args;
              DAST._IType _3194___mcc_h887 = _source141.dtor_result;
              {
                RAST._IExpr _out964;
                DCOMP._IOwnership _out965;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out964, out _out965, out _out966);
                r = _out964;
                resultingOwnership = _out965;
                readIdents = _out966;
              }
            } else if (_source141.is_Primitive) {
              DAST._IPrimitive _3195___mcc_h890 = _source141.dtor_Primitive_a0;
              DAST._IPrimitive _source143 = _3195___mcc_h890;
              if (_source143.is_Int) {
                {
                  RAST._IExpr _3196_recursiveGen;
                  DCOMP._IOwnership _3197___v75;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3198_recIdents;
                  RAST._IExpr _out967;
                  DCOMP._IOwnership _out968;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out969;
                  (this).GenExpr(_2697_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out967, out _out968, out _out969);
                  _3196_recursiveGen = _out967;
                  _3197___v75 = _out968;
                  _3198_recIdents = _out969;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_3196_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                  RAST._IExpr _out970;
                  DCOMP._IOwnership _out971;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out970, out _out971);
                  r = _out970;
                  resultingOwnership = _out971;
                  readIdents = _3198_recIdents;
                }
              } else if (_source143.is_Real) {
                {
                  RAST._IExpr _out972;
                  DCOMP._IOwnership _out973;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out972, out _out973, out _out974);
                  r = _out972;
                  resultingOwnership = _out973;
                  readIdents = _out974;
                }
              } else if (_source143.is_String) {
                {
                  RAST._IExpr _out975;
                  DCOMP._IOwnership _out976;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out977;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out975, out _out976, out _out977);
                  r = _out975;
                  resultingOwnership = _out976;
                  readIdents = _out977;
                }
              } else if (_source143.is_Bool) {
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
            } else if (_source141.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3199___mcc_h892 = _source141.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _3200___mcc_h894 = _source141.dtor_TypeArg_a0;
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
          } else if (_source137.is_String) {
            DAST._IType _source144 = _2704___mcc_h1;
            if (_source144.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3201___mcc_h896 = _source144.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _3202___mcc_h897 = _source144.dtor_typeArgs;
              DAST._IResolvedType _3203___mcc_h898 = _source144.dtor_resolved;
              DAST._IResolvedType _source145 = _3203___mcc_h898;
              if (_source145.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3204___mcc_h902 = _source145.dtor_path;
                {
                  RAST._IExpr _out990;
                  DCOMP._IOwnership _out991;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out992;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out990, out _out991, out _out992);
                  r = _out990;
                  resultingOwnership = _out991;
                  readIdents = _out992;
                }
              } else if (_source145.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3205___mcc_h904 = _source145.dtor_path;
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
                DAST._IType _3206___mcc_h906 = _source145.dtor_baseType;
                DAST._INewtypeRange _3207___mcc_h907 = _source145.dtor_range;
                bool _3208___mcc_h908 = _source145.dtor_erase;
                bool _3209_erase = _3208___mcc_h908;
                DAST._INewtypeRange _3210_range = _3207___mcc_h907;
                DAST._IType _3211_b = _3206___mcc_h906;
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
            } else if (_source144.is_Nullable) {
              DAST._IType _3212___mcc_h912 = _source144.dtor_Nullable_a0;
              {
                RAST._IExpr _out999;
                DCOMP._IOwnership _out1000;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1001;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out999, out _out1000, out _out1001);
                r = _out999;
                resultingOwnership = _out1000;
                readIdents = _out1001;
              }
            } else if (_source144.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3213___mcc_h914 = _source144.dtor_Tuple_a0;
              {
                RAST._IExpr _out1002;
                DCOMP._IOwnership _out1003;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1004;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1002, out _out1003, out _out1004);
                r = _out1002;
                resultingOwnership = _out1003;
                readIdents = _out1004;
              }
            } else if (_source144.is_Array) {
              DAST._IType _3214___mcc_h916 = _source144.dtor_element;
              BigInteger _3215___mcc_h917 = _source144.dtor_dims;
              {
                RAST._IExpr _out1005;
                DCOMP._IOwnership _out1006;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1007;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1005, out _out1006, out _out1007);
                r = _out1005;
                resultingOwnership = _out1006;
                readIdents = _out1007;
              }
            } else if (_source144.is_Seq) {
              DAST._IType _3216___mcc_h920 = _source144.dtor_element;
              {
                RAST._IExpr _out1008;
                DCOMP._IOwnership _out1009;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1010;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1008, out _out1009, out _out1010);
                r = _out1008;
                resultingOwnership = _out1009;
                readIdents = _out1010;
              }
            } else if (_source144.is_Set) {
              DAST._IType _3217___mcc_h922 = _source144.dtor_element;
              {
                RAST._IExpr _out1011;
                DCOMP._IOwnership _out1012;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1013;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1011, out _out1012, out _out1013);
                r = _out1011;
                resultingOwnership = _out1012;
                readIdents = _out1013;
              }
            } else if (_source144.is_Multiset) {
              DAST._IType _3218___mcc_h924 = _source144.dtor_element;
              {
                RAST._IExpr _out1014;
                DCOMP._IOwnership _out1015;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1016;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1014, out _out1015, out _out1016);
                r = _out1014;
                resultingOwnership = _out1015;
                readIdents = _out1016;
              }
            } else if (_source144.is_Map) {
              DAST._IType _3219___mcc_h926 = _source144.dtor_key;
              DAST._IType _3220___mcc_h927 = _source144.dtor_value;
              {
                RAST._IExpr _out1017;
                DCOMP._IOwnership _out1018;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1019;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1017, out _out1018, out _out1019);
                r = _out1017;
                resultingOwnership = _out1018;
                readIdents = _out1019;
              }
            } else if (_source144.is_SetBuilder) {
              DAST._IType _3221___mcc_h930 = _source144.dtor_element;
              {
                RAST._IExpr _out1020;
                DCOMP._IOwnership _out1021;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1022;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1020, out _out1021, out _out1022);
                r = _out1020;
                resultingOwnership = _out1021;
                readIdents = _out1022;
              }
            } else if (_source144.is_MapBuilder) {
              DAST._IType _3222___mcc_h932 = _source144.dtor_key;
              DAST._IType _3223___mcc_h933 = _source144.dtor_value;
              {
                RAST._IExpr _out1023;
                DCOMP._IOwnership _out1024;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1025;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1023, out _out1024, out _out1025);
                r = _out1023;
                resultingOwnership = _out1024;
                readIdents = _out1025;
              }
            } else if (_source144.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3224___mcc_h936 = _source144.dtor_args;
              DAST._IType _3225___mcc_h937 = _source144.dtor_result;
              {
                RAST._IExpr _out1026;
                DCOMP._IOwnership _out1027;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1028;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1026, out _out1027, out _out1028);
                r = _out1026;
                resultingOwnership = _out1027;
                readIdents = _out1028;
              }
            } else if (_source144.is_Primitive) {
              DAST._IPrimitive _3226___mcc_h940 = _source144.dtor_Primitive_a0;
              {
                RAST._IExpr _out1029;
                DCOMP._IOwnership _out1030;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1031;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1029, out _out1030, out _out1031);
                r = _out1029;
                resultingOwnership = _out1030;
                readIdents = _out1031;
              }
            } else if (_source144.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3227___mcc_h942 = _source144.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _3228___mcc_h944 = _source144.dtor_TypeArg_a0;
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
          } else if (_source137.is_Bool) {
            DAST._IType _source146 = _2704___mcc_h1;
            if (_source146.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3229___mcc_h946 = _source146.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _3230___mcc_h947 = _source146.dtor_typeArgs;
              DAST._IResolvedType _3231___mcc_h948 = _source146.dtor_resolved;
              DAST._IResolvedType _source147 = _3231___mcc_h948;
              if (_source147.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3232___mcc_h952 = _source147.dtor_path;
                {
                  RAST._IExpr _out1038;
                  DCOMP._IOwnership _out1039;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1040;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1038, out _out1039, out _out1040);
                  r = _out1038;
                  resultingOwnership = _out1039;
                  readIdents = _out1040;
                }
              } else if (_source147.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3233___mcc_h954 = _source147.dtor_path;
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
                DAST._IType _3234___mcc_h956 = _source147.dtor_baseType;
                DAST._INewtypeRange _3235___mcc_h957 = _source147.dtor_range;
                bool _3236___mcc_h958 = _source147.dtor_erase;
                bool _3237_erase = _3236___mcc_h958;
                DAST._INewtypeRange _3238_range = _3235___mcc_h957;
                DAST._IType _3239_b = _3234___mcc_h956;
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
            } else if (_source146.is_Nullable) {
              DAST._IType _3240___mcc_h962 = _source146.dtor_Nullable_a0;
              {
                RAST._IExpr _out1047;
                DCOMP._IOwnership _out1048;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1049;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1047, out _out1048, out _out1049);
                r = _out1047;
                resultingOwnership = _out1048;
                readIdents = _out1049;
              }
            } else if (_source146.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3241___mcc_h964 = _source146.dtor_Tuple_a0;
              {
                RAST._IExpr _out1050;
                DCOMP._IOwnership _out1051;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1052;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1050, out _out1051, out _out1052);
                r = _out1050;
                resultingOwnership = _out1051;
                readIdents = _out1052;
              }
            } else if (_source146.is_Array) {
              DAST._IType _3242___mcc_h966 = _source146.dtor_element;
              BigInteger _3243___mcc_h967 = _source146.dtor_dims;
              {
                RAST._IExpr _out1053;
                DCOMP._IOwnership _out1054;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1053, out _out1054, out _out1055);
                r = _out1053;
                resultingOwnership = _out1054;
                readIdents = _out1055;
              }
            } else if (_source146.is_Seq) {
              DAST._IType _3244___mcc_h970 = _source146.dtor_element;
              {
                RAST._IExpr _out1056;
                DCOMP._IOwnership _out1057;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1058;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1056, out _out1057, out _out1058);
                r = _out1056;
                resultingOwnership = _out1057;
                readIdents = _out1058;
              }
            } else if (_source146.is_Set) {
              DAST._IType _3245___mcc_h972 = _source146.dtor_element;
              {
                RAST._IExpr _out1059;
                DCOMP._IOwnership _out1060;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1061;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1059, out _out1060, out _out1061);
                r = _out1059;
                resultingOwnership = _out1060;
                readIdents = _out1061;
              }
            } else if (_source146.is_Multiset) {
              DAST._IType _3246___mcc_h974 = _source146.dtor_element;
              {
                RAST._IExpr _out1062;
                DCOMP._IOwnership _out1063;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1064;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1062, out _out1063, out _out1064);
                r = _out1062;
                resultingOwnership = _out1063;
                readIdents = _out1064;
              }
            } else if (_source146.is_Map) {
              DAST._IType _3247___mcc_h976 = _source146.dtor_key;
              DAST._IType _3248___mcc_h977 = _source146.dtor_value;
              {
                RAST._IExpr _out1065;
                DCOMP._IOwnership _out1066;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1065, out _out1066, out _out1067);
                r = _out1065;
                resultingOwnership = _out1066;
                readIdents = _out1067;
              }
            } else if (_source146.is_SetBuilder) {
              DAST._IType _3249___mcc_h980 = _source146.dtor_element;
              {
                RAST._IExpr _out1068;
                DCOMP._IOwnership _out1069;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1070;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1068, out _out1069, out _out1070);
                r = _out1068;
                resultingOwnership = _out1069;
                readIdents = _out1070;
              }
            } else if (_source146.is_MapBuilder) {
              DAST._IType _3250___mcc_h982 = _source146.dtor_key;
              DAST._IType _3251___mcc_h983 = _source146.dtor_value;
              {
                RAST._IExpr _out1071;
                DCOMP._IOwnership _out1072;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1073;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1071, out _out1072, out _out1073);
                r = _out1071;
                resultingOwnership = _out1072;
                readIdents = _out1073;
              }
            } else if (_source146.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3252___mcc_h986 = _source146.dtor_args;
              DAST._IType _3253___mcc_h987 = _source146.dtor_result;
              {
                RAST._IExpr _out1074;
                DCOMP._IOwnership _out1075;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1076;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1074, out _out1075, out _out1076);
                r = _out1074;
                resultingOwnership = _out1075;
                readIdents = _out1076;
              }
            } else if (_source146.is_Primitive) {
              DAST._IPrimitive _3254___mcc_h990 = _source146.dtor_Primitive_a0;
              {
                RAST._IExpr _out1077;
                DCOMP._IOwnership _out1078;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1077, out _out1078, out _out1079);
                r = _out1077;
                resultingOwnership = _out1078;
                readIdents = _out1079;
              }
            } else if (_source146.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3255___mcc_h992 = _source146.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _3256___mcc_h994 = _source146.dtor_TypeArg_a0;
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
            DAST._IType _source148 = _2704___mcc_h1;
            if (_source148.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3257___mcc_h996 = _source148.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _3258___mcc_h997 = _source148.dtor_typeArgs;
              DAST._IResolvedType _3259___mcc_h998 = _source148.dtor_resolved;
              DAST._IResolvedType _source149 = _3259___mcc_h998;
              if (_source149.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3260___mcc_h1002 = _source149.dtor_path;
                {
                  RAST._IExpr _out1086;
                  DCOMP._IOwnership _out1087;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1088;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1086, out _out1087, out _out1088);
                  r = _out1086;
                  resultingOwnership = _out1087;
                  readIdents = _out1088;
                }
              } else if (_source149.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3261___mcc_h1004 = _source149.dtor_path;
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
                DAST._IType _3262___mcc_h1006 = _source149.dtor_baseType;
                DAST._INewtypeRange _3263___mcc_h1007 = _source149.dtor_range;
                bool _3264___mcc_h1008 = _source149.dtor_erase;
                bool _3265_erase = _3264___mcc_h1008;
                DAST._INewtypeRange _3266_range = _3263___mcc_h1007;
                DAST._IType _3267_b = _3262___mcc_h1006;
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
            } else if (_source148.is_Nullable) {
              DAST._IType _3268___mcc_h1012 = _source148.dtor_Nullable_a0;
              {
                RAST._IExpr _out1095;
                DCOMP._IOwnership _out1096;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1097;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1095, out _out1096, out _out1097);
                r = _out1095;
                resultingOwnership = _out1096;
                readIdents = _out1097;
              }
            } else if (_source148.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3269___mcc_h1014 = _source148.dtor_Tuple_a0;
              {
                RAST._IExpr _out1098;
                DCOMP._IOwnership _out1099;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1098, out _out1099, out _out1100);
                r = _out1098;
                resultingOwnership = _out1099;
                readIdents = _out1100;
              }
            } else if (_source148.is_Array) {
              DAST._IType _3270___mcc_h1016 = _source148.dtor_element;
              BigInteger _3271___mcc_h1017 = _source148.dtor_dims;
              {
                RAST._IExpr _out1101;
                DCOMP._IOwnership _out1102;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1103;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1101, out _out1102, out _out1103);
                r = _out1101;
                resultingOwnership = _out1102;
                readIdents = _out1103;
              }
            } else if (_source148.is_Seq) {
              DAST._IType _3272___mcc_h1020 = _source148.dtor_element;
              {
                RAST._IExpr _out1104;
                DCOMP._IOwnership _out1105;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1106;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1104, out _out1105, out _out1106);
                r = _out1104;
                resultingOwnership = _out1105;
                readIdents = _out1106;
              }
            } else if (_source148.is_Set) {
              DAST._IType _3273___mcc_h1022 = _source148.dtor_element;
              {
                RAST._IExpr _out1107;
                DCOMP._IOwnership _out1108;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1109;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1107, out _out1108, out _out1109);
                r = _out1107;
                resultingOwnership = _out1108;
                readIdents = _out1109;
              }
            } else if (_source148.is_Multiset) {
              DAST._IType _3274___mcc_h1024 = _source148.dtor_element;
              {
                RAST._IExpr _out1110;
                DCOMP._IOwnership _out1111;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1110, out _out1111, out _out1112);
                r = _out1110;
                resultingOwnership = _out1111;
                readIdents = _out1112;
              }
            } else if (_source148.is_Map) {
              DAST._IType _3275___mcc_h1026 = _source148.dtor_key;
              DAST._IType _3276___mcc_h1027 = _source148.dtor_value;
              {
                RAST._IExpr _out1113;
                DCOMP._IOwnership _out1114;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1115;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1113, out _out1114, out _out1115);
                r = _out1113;
                resultingOwnership = _out1114;
                readIdents = _out1115;
              }
            } else if (_source148.is_SetBuilder) {
              DAST._IType _3277___mcc_h1030 = _source148.dtor_element;
              {
                RAST._IExpr _out1116;
                DCOMP._IOwnership _out1117;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1118;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1116, out _out1117, out _out1118);
                r = _out1116;
                resultingOwnership = _out1117;
                readIdents = _out1118;
              }
            } else if (_source148.is_MapBuilder) {
              DAST._IType _3278___mcc_h1032 = _source148.dtor_key;
              DAST._IType _3279___mcc_h1033 = _source148.dtor_value;
              {
                RAST._IExpr _out1119;
                DCOMP._IOwnership _out1120;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1121;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1119, out _out1120, out _out1121);
                r = _out1119;
                resultingOwnership = _out1120;
                readIdents = _out1121;
              }
            } else if (_source148.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3280___mcc_h1036 = _source148.dtor_args;
              DAST._IType _3281___mcc_h1037 = _source148.dtor_result;
              {
                RAST._IExpr _out1122;
                DCOMP._IOwnership _out1123;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1122, out _out1123, out _out1124);
                r = _out1122;
                resultingOwnership = _out1123;
                readIdents = _out1124;
              }
            } else if (_source148.is_Primitive) {
              DAST._IPrimitive _3282___mcc_h1040 = _source148.dtor_Primitive_a0;
              DAST._IPrimitive _source150 = _3282___mcc_h1040;
              if (_source150.is_Int) {
                {
                  RAST._IType _3283_rhsType;
                  RAST._IType _out1125;
                  _out1125 = (this).GenType(_2698_fromTpe, true, false);
                  _3283_rhsType = _out1125;
                  RAST._IExpr _3284_recursiveGen;
                  DCOMP._IOwnership _3285___v81;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3286_recIdents;
                  RAST._IExpr _out1126;
                  DCOMP._IOwnership _out1127;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1128;
                  (this).GenExpr(_2697_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1126, out _out1127, out _out1128);
                  _3284_recursiveGen = _out1126;
                  _3285___v81 = _out1127;
                  _3286_recIdents = _out1128;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::BigInt::from("), (_3284_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)}")));
                  RAST._IExpr _out1129;
                  DCOMP._IOwnership _out1130;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1129, out _out1130);
                  r = _out1129;
                  resultingOwnership = _out1130;
                  readIdents = _3286_recIdents;
                }
              } else if (_source150.is_Real) {
                {
                  RAST._IExpr _out1131;
                  DCOMP._IOwnership _out1132;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1133;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1131, out _out1132, out _out1133);
                  r = _out1131;
                  resultingOwnership = _out1132;
                  readIdents = _out1133;
                }
              } else if (_source150.is_String) {
                {
                  RAST._IExpr _out1134;
                  DCOMP._IOwnership _out1135;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1134, out _out1135, out _out1136);
                  r = _out1134;
                  resultingOwnership = _out1135;
                  readIdents = _out1136;
                }
              } else if (_source150.is_Bool) {
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
            } else if (_source148.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3287___mcc_h1042 = _source148.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _3288___mcc_h1044 = _source148.dtor_TypeArg_a0;
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
        } else if (_source109.is_Passthrough) {
          Dafny.ISequence<Dafny.Rune> _3289___mcc_h1046 = _source109.dtor_Passthrough_a0;
          DAST._IType _source151 = _2704___mcc_h1;
          if (_source151.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3290___mcc_h1050 = _source151.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _3291___mcc_h1051 = _source151.dtor_typeArgs;
            DAST._IResolvedType _3292___mcc_h1052 = _source151.dtor_resolved;
            DAST._IResolvedType _source152 = _3292___mcc_h1052;
            if (_source152.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3293___mcc_h1056 = _source152.dtor_path;
              {
                RAST._IExpr _out1149;
                DCOMP._IOwnership _out1150;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1151;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1149, out _out1150, out _out1151);
                r = _out1149;
                resultingOwnership = _out1150;
                readIdents = _out1151;
              }
            } else if (_source152.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3294___mcc_h1058 = _source152.dtor_path;
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
              DAST._IType _3295___mcc_h1060 = _source152.dtor_baseType;
              DAST._INewtypeRange _3296___mcc_h1061 = _source152.dtor_range;
              bool _3297___mcc_h1062 = _source152.dtor_erase;
              bool _3298_erase = _3297___mcc_h1062;
              DAST._INewtypeRange _3299_range = _3296___mcc_h1061;
              DAST._IType _3300_b = _3295___mcc_h1060;
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
          } else if (_source151.is_Nullable) {
            DAST._IType _3301___mcc_h1066 = _source151.dtor_Nullable_a0;
            {
              RAST._IExpr _out1158;
              DCOMP._IOwnership _out1159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1160;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1158, out _out1159, out _out1160);
              r = _out1158;
              resultingOwnership = _out1159;
              readIdents = _out1160;
            }
          } else if (_source151.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3302___mcc_h1068 = _source151.dtor_Tuple_a0;
            {
              RAST._IExpr _out1161;
              DCOMP._IOwnership _out1162;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1163;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1161, out _out1162, out _out1163);
              r = _out1161;
              resultingOwnership = _out1162;
              readIdents = _out1163;
            }
          } else if (_source151.is_Array) {
            DAST._IType _3303___mcc_h1070 = _source151.dtor_element;
            BigInteger _3304___mcc_h1071 = _source151.dtor_dims;
            {
              RAST._IExpr _out1164;
              DCOMP._IOwnership _out1165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1166;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1164, out _out1165, out _out1166);
              r = _out1164;
              resultingOwnership = _out1165;
              readIdents = _out1166;
            }
          } else if (_source151.is_Seq) {
            DAST._IType _3305___mcc_h1074 = _source151.dtor_element;
            {
              RAST._IExpr _out1167;
              DCOMP._IOwnership _out1168;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1167, out _out1168, out _out1169);
              r = _out1167;
              resultingOwnership = _out1168;
              readIdents = _out1169;
            }
          } else if (_source151.is_Set) {
            DAST._IType _3306___mcc_h1076 = _source151.dtor_element;
            {
              RAST._IExpr _out1170;
              DCOMP._IOwnership _out1171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1172;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1170, out _out1171, out _out1172);
              r = _out1170;
              resultingOwnership = _out1171;
              readIdents = _out1172;
            }
          } else if (_source151.is_Multiset) {
            DAST._IType _3307___mcc_h1078 = _source151.dtor_element;
            {
              RAST._IExpr _out1173;
              DCOMP._IOwnership _out1174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1175;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1173, out _out1174, out _out1175);
              r = _out1173;
              resultingOwnership = _out1174;
              readIdents = _out1175;
            }
          } else if (_source151.is_Map) {
            DAST._IType _3308___mcc_h1080 = _source151.dtor_key;
            DAST._IType _3309___mcc_h1081 = _source151.dtor_value;
            {
              RAST._IExpr _out1176;
              DCOMP._IOwnership _out1177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1178;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1176, out _out1177, out _out1178);
              r = _out1176;
              resultingOwnership = _out1177;
              readIdents = _out1178;
            }
          } else if (_source151.is_SetBuilder) {
            DAST._IType _3310___mcc_h1084 = _source151.dtor_element;
            {
              RAST._IExpr _out1179;
              DCOMP._IOwnership _out1180;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1179, out _out1180, out _out1181);
              r = _out1179;
              resultingOwnership = _out1180;
              readIdents = _out1181;
            }
          } else if (_source151.is_MapBuilder) {
            DAST._IType _3311___mcc_h1086 = _source151.dtor_key;
            DAST._IType _3312___mcc_h1087 = _source151.dtor_value;
            {
              RAST._IExpr _out1182;
              DCOMP._IOwnership _out1183;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1184;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1182, out _out1183, out _out1184);
              r = _out1182;
              resultingOwnership = _out1183;
              readIdents = _out1184;
            }
          } else if (_source151.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3313___mcc_h1090 = _source151.dtor_args;
            DAST._IType _3314___mcc_h1091 = _source151.dtor_result;
            {
              RAST._IExpr _out1185;
              DCOMP._IOwnership _out1186;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1187;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1185, out _out1186, out _out1187);
              r = _out1185;
              resultingOwnership = _out1186;
              readIdents = _out1187;
            }
          } else if (_source151.is_Primitive) {
            DAST._IPrimitive _3315___mcc_h1094 = _source151.dtor_Primitive_a0;
            DAST._IPrimitive _source153 = _3315___mcc_h1094;
            if (_source153.is_Int) {
              {
                RAST._IType _3316_rhsType;
                RAST._IType _out1188;
                _out1188 = (this).GenType(_2698_fromTpe, true, false);
                _3316_rhsType = _out1188;
                RAST._IExpr _3317_recursiveGen;
                DCOMP._IOwnership _3318___v79;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3319_recIdents;
                RAST._IExpr _out1189;
                DCOMP._IOwnership _out1190;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1191;
                (this).GenExpr(_2697_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1189, out _out1190, out _out1191);
                _3317_recursiveGen = _out1189;
                _3318___v79 = _out1190;
                _3319_recIdents = _out1191;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_3317_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                RAST._IExpr _out1192;
                DCOMP._IOwnership _out1193;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1192, out _out1193);
                r = _out1192;
                resultingOwnership = _out1193;
                readIdents = _3319_recIdents;
              }
            } else if (_source153.is_Real) {
              {
                RAST._IExpr _out1194;
                DCOMP._IOwnership _out1195;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1196;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1194, out _out1195, out _out1196);
                r = _out1194;
                resultingOwnership = _out1195;
                readIdents = _out1196;
              }
            } else if (_source153.is_String) {
              {
                RAST._IExpr _out1197;
                DCOMP._IOwnership _out1198;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1199;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1197, out _out1198, out _out1199);
                r = _out1197;
                resultingOwnership = _out1198;
                readIdents = _out1199;
              }
            } else if (_source153.is_Bool) {
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
          } else if (_source151.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3320___mcc_h1096 = _source151.dtor_Passthrough_a0;
            {
              RAST._IExpr _3321_recursiveGen;
              DCOMP._IOwnership _3322___v84;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3323_recIdents;
              RAST._IExpr _out1206;
              DCOMP._IOwnership _out1207;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1208;
              (this).GenExpr(_2697_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1206, out _out1207, out _out1208);
              _3321_recursiveGen = _out1206;
              _3322___v84 = _out1207;
              _3323_recIdents = _out1208;
              RAST._IType _3324_toTpeGen;
              RAST._IType _out1209;
              _out1209 = (this).GenType(_2699_toTpe, true, false);
              _3324_toTpeGen = _out1209;
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_3321_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_3324_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
              RAST._IExpr _out1210;
              DCOMP._IOwnership _out1211;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1210, out _out1211);
              r = _out1210;
              resultingOwnership = _out1211;
              readIdents = _3323_recIdents;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3325___mcc_h1098 = _source151.dtor_TypeArg_a0;
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
          Dafny.ISequence<Dafny.Rune> _3326___mcc_h1100 = _source109.dtor_TypeArg_a0;
          DAST._IType _source154 = _2704___mcc_h1;
          if (_source154.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3327___mcc_h1104 = _source154.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _3328___mcc_h1105 = _source154.dtor_typeArgs;
            DAST._IResolvedType _3329___mcc_h1106 = _source154.dtor_resolved;
            DAST._IResolvedType _source155 = _3329___mcc_h1106;
            if (_source155.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3330___mcc_h1110 = _source155.dtor_path;
              {
                RAST._IExpr _out1215;
                DCOMP._IOwnership _out1216;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1217;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1215, out _out1216, out _out1217);
                r = _out1215;
                resultingOwnership = _out1216;
                readIdents = _out1217;
              }
            } else if (_source155.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3331___mcc_h1112 = _source155.dtor_path;
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
              DAST._IType _3332___mcc_h1114 = _source155.dtor_baseType;
              DAST._INewtypeRange _3333___mcc_h1115 = _source155.dtor_range;
              bool _3334___mcc_h1116 = _source155.dtor_erase;
              bool _3335_erase = _3334___mcc_h1116;
              DAST._INewtypeRange _3336_range = _3333___mcc_h1115;
              DAST._IType _3337_b = _3332___mcc_h1114;
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
          } else if (_source154.is_Nullable) {
            DAST._IType _3338___mcc_h1120 = _source154.dtor_Nullable_a0;
            {
              RAST._IExpr _out1224;
              DCOMP._IOwnership _out1225;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1224, out _out1225, out _out1226);
              r = _out1224;
              resultingOwnership = _out1225;
              readIdents = _out1226;
            }
          } else if (_source154.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3339___mcc_h1122 = _source154.dtor_Tuple_a0;
            {
              RAST._IExpr _out1227;
              DCOMP._IOwnership _out1228;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1229;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1227, out _out1228, out _out1229);
              r = _out1227;
              resultingOwnership = _out1228;
              readIdents = _out1229;
            }
          } else if (_source154.is_Array) {
            DAST._IType _3340___mcc_h1124 = _source154.dtor_element;
            BigInteger _3341___mcc_h1125 = _source154.dtor_dims;
            {
              RAST._IExpr _out1230;
              DCOMP._IOwnership _out1231;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1232;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1230, out _out1231, out _out1232);
              r = _out1230;
              resultingOwnership = _out1231;
              readIdents = _out1232;
            }
          } else if (_source154.is_Seq) {
            DAST._IType _3342___mcc_h1128 = _source154.dtor_element;
            {
              RAST._IExpr _out1233;
              DCOMP._IOwnership _out1234;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1235;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1233, out _out1234, out _out1235);
              r = _out1233;
              resultingOwnership = _out1234;
              readIdents = _out1235;
            }
          } else if (_source154.is_Set) {
            DAST._IType _3343___mcc_h1130 = _source154.dtor_element;
            {
              RAST._IExpr _out1236;
              DCOMP._IOwnership _out1237;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1238;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1236, out _out1237, out _out1238);
              r = _out1236;
              resultingOwnership = _out1237;
              readIdents = _out1238;
            }
          } else if (_source154.is_Multiset) {
            DAST._IType _3344___mcc_h1132 = _source154.dtor_element;
            {
              RAST._IExpr _out1239;
              DCOMP._IOwnership _out1240;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1241;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1239, out _out1240, out _out1241);
              r = _out1239;
              resultingOwnership = _out1240;
              readIdents = _out1241;
            }
          } else if (_source154.is_Map) {
            DAST._IType _3345___mcc_h1134 = _source154.dtor_key;
            DAST._IType _3346___mcc_h1135 = _source154.dtor_value;
            {
              RAST._IExpr _out1242;
              DCOMP._IOwnership _out1243;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1244;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1242, out _out1243, out _out1244);
              r = _out1242;
              resultingOwnership = _out1243;
              readIdents = _out1244;
            }
          } else if (_source154.is_SetBuilder) {
            DAST._IType _3347___mcc_h1138 = _source154.dtor_element;
            {
              RAST._IExpr _out1245;
              DCOMP._IOwnership _out1246;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1245, out _out1246, out _out1247);
              r = _out1245;
              resultingOwnership = _out1246;
              readIdents = _out1247;
            }
          } else if (_source154.is_MapBuilder) {
            DAST._IType _3348___mcc_h1140 = _source154.dtor_key;
            DAST._IType _3349___mcc_h1141 = _source154.dtor_value;
            {
              RAST._IExpr _out1248;
              DCOMP._IOwnership _out1249;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1250;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1248, out _out1249, out _out1250);
              r = _out1248;
              resultingOwnership = _out1249;
              readIdents = _out1250;
            }
          } else if (_source154.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3350___mcc_h1144 = _source154.dtor_args;
            DAST._IType _3351___mcc_h1145 = _source154.dtor_result;
            {
              RAST._IExpr _out1251;
              DCOMP._IOwnership _out1252;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1253;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1251, out _out1252, out _out1253);
              r = _out1251;
              resultingOwnership = _out1252;
              readIdents = _out1253;
            }
          } else if (_source154.is_Primitive) {
            DAST._IPrimitive _3352___mcc_h1148 = _source154.dtor_Primitive_a0;
            {
              RAST._IExpr _out1254;
              DCOMP._IOwnership _out1255;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1256;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1254, out _out1255, out _out1256);
              r = _out1254;
              resultingOwnership = _out1255;
              readIdents = _out1256;
            }
          } else if (_source154.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3353___mcc_h1150 = _source154.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _3354___mcc_h1152 = _source154.dtor_TypeArg_a0;
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
      DAST._IExpression _source156 = e;
      if (_source156.is_Literal) {
        DAST._ILiteral _3355___mcc_h0 = _source156.dtor_Literal_a0;
        RAST._IExpr _out1263;
        DCOMP._IOwnership _out1264;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1265;
        (this).GenExprLiteral(e, selfIdent, @params, expectedOwnership, out _out1263, out _out1264, out _out1265);
        r = _out1263;
        resultingOwnership = _out1264;
        readIdents = _out1265;
      } else if (_source156.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _3356___mcc_h1 = _source156.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _3357_name = _3356___mcc_h1;
        {
          r = RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent(_3357_name));
          bool _3358_currentlyBorrowed;
          _3358_currentlyBorrowed = (@params).Contains(_3357_name);
          if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
            r = RAST.__default.BorrowMut(r);
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
          } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
            r = RAST.__default.Clone(r);
            resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          } else if (_3358_currentlyBorrowed) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          } else {
            r = RAST.__default.Borrow(r);
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3357_name);
          return ;
        }
      } else if (_source156.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3359___mcc_h2 = _source156.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3360_path = _3359___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _3361_p;
          Dafny.ISequence<Dafny.Rune> _out1266;
          _out1266 = DCOMP.COMP.GenPath(_3360_path);
          _3361_p = _out1266;
          r = RAST.Expr.create_RawExpr(_3361_p);
          RAST._IExpr _out1267;
          DCOMP._IOwnership _out1268;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1267, out _out1268);
          r = _out1267;
          resultingOwnership = _out1268;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source156.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _3362___mcc_h3 = _source156.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _3363_values = _3362___mcc_h3;
        {
          Dafny.ISequence<Dafny.Rune> _3364_s;
          _3364_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3365_i;
          _3365_i = BigInteger.Zero;
          while ((_3365_i) < (new BigInteger((_3363_values).Count))) {
            if ((_3365_i).Sign == 1) {
              _3364_s = Dafny.Sequence<Dafny.Rune>.Concat(_3364_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            RAST._IExpr _3366_recursiveGen;
            DCOMP._IOwnership _3367___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3368_recIdents;
            RAST._IExpr _out1269;
            DCOMP._IOwnership _out1270;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1271;
            (this).GenExpr((_3363_values).Select(_3365_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1269, out _out1270, out _out1271);
            _3366_recursiveGen = _out1269;
            _3367___v87 = _out1270;
            _3368_recIdents = _out1271;
            _3364_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3364_s, (_3366_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3368_recIdents);
            _3365_i = (_3365_i) + (BigInteger.One);
          }
          _3364_s = Dafny.Sequence<Dafny.Rune>.Concat(_3364_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          r = RAST.Expr.create_RawExpr(_3364_s);
          RAST._IExpr _out1272;
          DCOMP._IOwnership _out1273;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1272, out _out1273);
          r = _out1272;
          resultingOwnership = _out1273;
          return ;
        }
      } else if (_source156.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3369___mcc_h4 = _source156.dtor_path;
        Dafny.ISequence<DAST._IType> _3370___mcc_h5 = _source156.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _3371___mcc_h6 = _source156.dtor_args;
        Dafny.ISequence<DAST._IExpression> _3372_args = _3371___mcc_h6;
        Dafny.ISequence<DAST._IType> _3373_typeArgs = _3370___mcc_h5;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3374_path = _3369___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _3375_path;
          Dafny.ISequence<Dafny.Rune> _out1274;
          _out1274 = DCOMP.COMP.GenPath(_3374_path);
          _3375_path = _out1274;
          Dafny.ISequence<Dafny.Rune> _3376_s;
          _3376_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _3375_path);
          if ((new BigInteger((_3373_typeArgs).Count)).Sign == 1) {
            BigInteger _3377_i;
            _3377_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IType> _3378_typeExprs;
            _3378_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            while ((_3377_i) < (new BigInteger((_3373_typeArgs).Count))) {
              RAST._IType _3379_typeExpr;
              RAST._IType _out1275;
              _out1275 = (this).GenType((_3373_typeArgs).Select(_3377_i), false, false);
              _3379_typeExpr = _out1275;
              _3378_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_3378_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_3379_typeExpr));
              _3377_i = (_3377_i) + (BigInteger.One);
            }
            _3376_s = Dafny.Sequence<Dafny.Rune>.Concat(_3376_s, (RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _3378_typeExprs))._ToString(DCOMP.__default.IND));
          }
          _3376_s = Dafny.Sequence<Dafny.Rune>.Concat(_3376_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3380_i;
          _3380_i = BigInteger.Zero;
          while ((_3380_i) < (new BigInteger((_3372_args).Count))) {
            if ((_3380_i).Sign == 1) {
              _3376_s = Dafny.Sequence<Dafny.Rune>.Concat(_3376_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IExpr _3381_recursiveGen;
            DCOMP._IOwnership _3382___v88;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3383_recIdents;
            RAST._IExpr _out1276;
            DCOMP._IOwnership _out1277;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1278;
            (this).GenExpr((_3372_args).Select(_3380_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1276, out _out1277, out _out1278);
            _3381_recursiveGen = _out1276;
            _3382___v88 = _out1277;
            _3383_recIdents = _out1278;
            _3376_s = Dafny.Sequence<Dafny.Rune>.Concat(_3376_s, (_3381_recursiveGen)._ToString(DCOMP.__default.IND));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3383_recIdents);
            _3380_i = (_3380_i) + (BigInteger.One);
          }
          _3376_s = Dafny.Sequence<Dafny.Rune>.Concat(_3376_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          r = RAST.Expr.create_RawExpr(_3376_s);
          RAST._IExpr _out1279;
          DCOMP._IOwnership _out1280;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1279, out _out1280);
          r = _out1279;
          resultingOwnership = _out1280;
          return ;
        }
      } else if (_source156.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _3384___mcc_h7 = _source156.dtor_dims;
        DAST._IType _3385___mcc_h8 = _source156.dtor_typ;
        DAST._IType _3386_typ = _3385___mcc_h8;
        Dafny.ISequence<DAST._IExpression> _3387_dims = _3384___mcc_h7;
        {
          BigInteger _3388_i;
          _3388_i = (new BigInteger((_3387_dims).Count)) - (BigInteger.One);
          RAST._IType _3389_genTyp;
          RAST._IType _out1281;
          _out1281 = (this).GenType(_3386_typ, false, false);
          _3389_genTyp = _out1281;
          Dafny.ISequence<Dafny.Rune> _3390_s;
          _3390_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3389_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_3388_i).Sign != -1) {
            RAST._IExpr _3391_recursiveGen;
            DCOMP._IOwnership _3392___v89;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3393_recIdents;
            RAST._IExpr _out1282;
            DCOMP._IOwnership _out1283;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1284;
            (this).GenExpr((_3387_dims).Select(_3388_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1282, out _out1283, out _out1284);
            _3391_recursiveGen = _out1282;
            _3392___v89 = _out1283;
            _3393_recIdents = _out1284;
            _3390_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _3390_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_3391_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3393_recIdents);
            _3388_i = (_3388_i) - (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(_3390_s);
          RAST._IExpr _out1285;
          DCOMP._IOwnership _out1286;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1285, out _out1286);
          r = _out1285;
          resultingOwnership = _out1286;
          return ;
        }
      } else if (_source156.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3394___mcc_h9 = _source156.dtor_path;
        Dafny.ISequence<DAST._IType> _3395___mcc_h10 = _source156.dtor_typeArgs;
        Dafny.ISequence<Dafny.Rune> _3396___mcc_h11 = _source156.dtor_variant;
        bool _3397___mcc_h12 = _source156.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3398___mcc_h13 = _source156.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3399_values = _3398___mcc_h13;
        bool _3400_isCo = _3397___mcc_h12;
        Dafny.ISequence<Dafny.Rune> _3401_variant = _3396___mcc_h11;
        Dafny.ISequence<DAST._IType> _3402_typeArgs = _3395___mcc_h10;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3403_path = _3394___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _3404_path;
          Dafny.ISequence<Dafny.Rune> _out1287;
          _out1287 = DCOMP.COMP.GenPath(_3403_path);
          _3404_path = _out1287;
          Dafny.ISequence<Dafny.Rune> _3405_s;
          _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _3404_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          if ((new BigInteger((_3402_typeArgs).Count)).Sign == 1) {
            _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
            BigInteger _3406_i;
            _3406_i = BigInteger.Zero;
            while ((_3406_i) < (new BigInteger((_3402_typeArgs).Count))) {
              if ((_3406_i).Sign == 1) {
                _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              RAST._IType _3407_typeExpr;
              RAST._IType _out1288;
              _out1288 = (this).GenType((_3402_typeArgs).Select(_3406_i), false, false);
              _3407_typeExpr = _out1288;
              _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, (_3407_typeExpr)._ToString(DCOMP.__default.IND));
              _3406_i = (_3406_i) + (BigInteger.One);
            }
            _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::"));
          }
          _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, DCOMP.__default.escapeIdent(_3401_variant));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3408_i;
          _3408_i = BigInteger.Zero;
          _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_3408_i) < (new BigInteger((_3399_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs60 = (_3399_values).Select(_3408_i);
            Dafny.ISequence<Dafny.Rune> _3409_name = _let_tmp_rhs60.dtor__0;
            DAST._IExpression _3410_value = _let_tmp_rhs60.dtor__1;
            if ((_3408_i).Sign == 1) {
              _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_3400_isCo) {
              RAST._IExpr _3411_recursiveGen;
              DCOMP._IOwnership _3412___v90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3413_recIdents;
              RAST._IExpr _out1289;
              DCOMP._IOwnership _out1290;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1291;
              (this).GenExpr(_3410_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out1289, out _out1290, out _out1291);
              _3411_recursiveGen = _out1289;
              _3412___v90 = _out1290;
              _3413_recIdents = _out1291;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3413_recIdents);
              Dafny.ISequence<Dafny.Rune> _3414_allReadCloned;
              _3414_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_3413_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _3415_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_3413_recIdents).Elements) {
                  _3415_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                  if ((_3413_recIdents).Contains(_3415_next)) {
                    goto after__ASSIGN_SUCH_THAT_2;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 2846)");
              after__ASSIGN_SUCH_THAT_2: ;
                _3414_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3414_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent(_3415_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), DCOMP.__default.escapeIdent(_3415_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _3413_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_3413_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3415_next));
              }
              _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, DCOMP.__default.escapeIdent(_3409_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _3414_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_3411_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              RAST._IExpr _3416_recursiveGen;
              DCOMP._IOwnership _3417___v91;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3418_recIdents;
              RAST._IExpr _out1292;
              DCOMP._IOwnership _out1293;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1294;
              (this).GenExpr(_3410_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1292, out _out1293, out _out1294);
              _3416_recursiveGen = _out1292;
              _3417___v91 = _out1293;
              _3418_recIdents = _out1294;
              _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, DCOMP.__default.escapeIdent(_3409_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_3416_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3418_recIdents);
            }
            _3408_i = (_3408_i) + (BigInteger.One);
          }
          _3405_s = Dafny.Sequence<Dafny.Rune>.Concat(_3405_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          r = RAST.Expr.create_RawExpr(_3405_s);
          RAST._IExpr _out1295;
          DCOMP._IOwnership _out1296;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1295, out _out1296);
          r = _out1295;
          resultingOwnership = _out1296;
          return ;
        }
      } else if (_source156.is_Convert) {
        DAST._IExpression _3419___mcc_h14 = _source156.dtor_value;
        DAST._IType _3420___mcc_h15 = _source156.dtor_from;
        DAST._IType _3421___mcc_h16 = _source156.dtor_typ;
        {
          RAST._IExpr _out1297;
          DCOMP._IOwnership _out1298;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1299;
          (this).GenExprConvert(e, selfIdent, @params, expectedOwnership, out _out1297, out _out1298, out _out1299);
          r = _out1297;
          resultingOwnership = _out1298;
          readIdents = _out1299;
        }
      } else if (_source156.is_SeqConstruct) {
        DAST._IExpression _3422___mcc_h17 = _source156.dtor_length;
        DAST._IExpression _3423___mcc_h18 = _source156.dtor_elem;
        DAST._IExpression _3424_expr = _3423___mcc_h18;
        DAST._IExpression _3425_length = _3422___mcc_h17;
        {
          RAST._IExpr _3426_recursiveGen;
          DCOMP._IOwnership _3427___v95;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3428_recIdents;
          RAST._IExpr _out1300;
          DCOMP._IOwnership _out1301;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1302;
          (this).GenExpr(_3424_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1300, out _out1301, out _out1302);
          _3426_recursiveGen = _out1300;
          _3427___v95 = _out1301;
          _3428_recIdents = _out1302;
          RAST._IExpr _3429_lengthGen;
          DCOMP._IOwnership _3430___v96;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3431_lengthIdents;
          RAST._IExpr _out1303;
          DCOMP._IOwnership _out1304;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
          (this).GenExpr(_3425_length, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1303, out _out1304, out _out1305);
          _3429_lengthGen = _out1303;
          _3430___v96 = _out1304;
          _3431_lengthIdents = _out1305;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_3426_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_3429_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer.0(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3428_recIdents, _3431_lengthIdents);
          RAST._IExpr _out1306;
          DCOMP._IOwnership _out1307;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1306, out _out1307);
          r = _out1306;
          resultingOwnership = _out1307;
          return ;
        }
      } else if (_source156.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _3432___mcc_h19 = _source156.dtor_elements;
        DAST._IType _3433___mcc_h20 = _source156.dtor_typ;
        DAST._IType _3434_typ = _3433___mcc_h20;
        Dafny.ISequence<DAST._IExpression> _3435_exprs = _3432___mcc_h19;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IType _3436_genTpe;
          RAST._IType _out1308;
          _out1308 = (this).GenType(_3434_typ, false, false);
          _3436_genTpe = _out1308;
          BigInteger _3437_i;
          _3437_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _3438_args;
          _3438_args = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_3437_i) < (new BigInteger((_3435_exprs).Count))) {
            RAST._IExpr _3439_recursiveGen;
            DCOMP._IOwnership _3440___v97;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3441_recIdents;
            RAST._IExpr _out1309;
            DCOMP._IOwnership _out1310;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1311;
            (this).GenExpr((_3435_exprs).Select(_3437_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1309, out _out1310, out _out1311);
            _3439_recursiveGen = _out1309;
            _3440___v97 = _out1310;
            _3441_recIdents = _out1311;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3441_recIdents);
            _3438_args = Dafny.Sequence<RAST._IExpr>.Concat(_3438_args, Dafny.Sequence<RAST._IExpr>.FromElements(_3439_recursiveGen));
            _3437_i = (_3437_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3438_args);
          if ((new BigInteger((_3438_args).Count)).Sign == 0) {
            r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_3436_genTpe));
          }
          RAST._IExpr _out1312;
          DCOMP._IOwnership _out1313;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1312, out _out1313);
          r = _out1312;
          resultingOwnership = _out1313;
          return ;
        }
      } else if (_source156.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _3442___mcc_h21 = _source156.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _3443_exprs = _3442___mcc_h21;
        {
          Dafny.ISequence<RAST._IExpr> _3444_generatedValues;
          _3444_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3445_i;
          _3445_i = BigInteger.Zero;
          while ((_3445_i) < (new BigInteger((_3443_exprs).Count))) {
            RAST._IExpr _3446_recursiveGen;
            DCOMP._IOwnership _3447___v98;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3448_recIdents;
            RAST._IExpr _out1314;
            DCOMP._IOwnership _out1315;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1316;
            (this).GenExpr((_3443_exprs).Select(_3445_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1314, out _out1315, out _out1316);
            _3446_recursiveGen = _out1314;
            _3447___v98 = _out1315;
            _3448_recIdents = _out1316;
            _3444_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_3444_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_3446_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3448_recIdents);
            _3445_i = (_3445_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3444_generatedValues);
          RAST._IExpr _out1317;
          DCOMP._IOwnership _out1318;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1317, out _out1318);
          r = _out1317;
          resultingOwnership = _out1318;
          return ;
        }
      } else if (_source156.is_MultisetValue) {
        Dafny.ISequence<DAST._IExpression> _3449___mcc_h22 = _source156.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _3450_exprs = _3449___mcc_h22;
        {
          Dafny.ISequence<RAST._IExpr> _3451_generatedValues;
          _3451_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3452_i;
          _3452_i = BigInteger.Zero;
          while ((_3452_i) < (new BigInteger((_3450_exprs).Count))) {
            RAST._IExpr _3453_recursiveGen;
            DCOMP._IOwnership _3454___v99;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3455_recIdents;
            RAST._IExpr _out1319;
            DCOMP._IOwnership _out1320;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1321;
            (this).GenExpr((_3450_exprs).Select(_3452_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1319, out _out1320, out _out1321);
            _3453_recursiveGen = _out1319;
            _3454___v99 = _out1320;
            _3455_recIdents = _out1321;
            _3451_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_3451_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_3453_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3455_recIdents);
            _3452_i = (_3452_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3451_generatedValues);
          RAST._IExpr _out1322;
          DCOMP._IOwnership _out1323;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1322, out _out1323);
          r = _out1322;
          resultingOwnership = _out1323;
          return ;
        }
      } else if (_source156.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3456___mcc_h23 = _source156.dtor_mapElems;
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3457_mapElems = _3456___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _3458_generatedValues;
          _3458_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3459_i;
          _3459_i = BigInteger.Zero;
          while ((_3459_i) < (new BigInteger((_3457_mapElems).Count))) {
            RAST._IExpr _3460_recursiveGenKey;
            DCOMP._IOwnership _3461___v101;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3462_recIdentsKey;
            RAST._IExpr _out1324;
            DCOMP._IOwnership _out1325;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1326;
            (this).GenExpr(((_3457_mapElems).Select(_3459_i)).dtor__0, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1324, out _out1325, out _out1326);
            _3460_recursiveGenKey = _out1324;
            _3461___v101 = _out1325;
            _3462_recIdentsKey = _out1326;
            RAST._IExpr _3463_recursiveGenValue;
            DCOMP._IOwnership _3464___v102;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3465_recIdentsValue;
            RAST._IExpr _out1327;
            DCOMP._IOwnership _out1328;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1329;
            (this).GenExpr(((_3457_mapElems).Select(_3459_i)).dtor__1, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1327, out _out1328, out _out1329);
            _3463_recursiveGenValue = _out1327;
            _3464___v102 = _out1328;
            _3465_recIdentsValue = _out1329;
            _3458_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_3458_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_3460_recursiveGenKey, _3463_recursiveGenValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3462_recIdentsKey), _3465_recIdentsValue);
            _3459_i = (_3459_i) + (BigInteger.One);
          }
          _3459_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _3466_arguments;
          _3466_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_3459_i) < (new BigInteger((_3458_generatedValues).Count))) {
            RAST._IExpr _3467_genKey;
            _3467_genKey = ((_3458_generatedValues).Select(_3459_i)).dtor__0;
            RAST._IExpr _3468_genValue;
            _3468_genValue = ((_3458_generatedValues).Select(_3459_i)).dtor__1;
            _3466_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3466_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _3467_genKey, _3468_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
            _3459_i = (_3459_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3466_arguments);
          RAST._IExpr _out1330;
          DCOMP._IOwnership _out1331;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1330, out _out1331);
          r = _out1330;
          resultingOwnership = _out1331;
          return ;
        }
      } else if (_source156.is_MapBuilder) {
        DAST._IType _3469___mcc_h24 = _source156.dtor_keyType;
        DAST._IType _3470___mcc_h25 = _source156.dtor_valueType;
        DAST._IType _3471_valueType = _3470___mcc_h25;
        DAST._IType _3472_keyType = _3469___mcc_h24;
        {
          RAST._IType _3473_kType;
          RAST._IType _out1332;
          _out1332 = (this).GenType(_3472_keyType, false, false);
          _3473_kType = _out1332;
          RAST._IType _3474_vType;
          RAST._IType _out1333;
          _out1333 = (this).GenType(_3471_valueType, false, false);
          _3474_vType = _out1333;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::MapBuilder::<"), (_3473_kType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), (_3474_vType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::new()")));
          RAST._IExpr _out1334;
          DCOMP._IOwnership _out1335;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1334, out _out1335);
          r = _out1334;
          resultingOwnership = _out1335;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source156.is_SeqUpdate) {
        DAST._IExpression _3475___mcc_h26 = _source156.dtor_expr;
        DAST._IExpression _3476___mcc_h27 = _source156.dtor_indexExpr;
        DAST._IExpression _3477___mcc_h28 = _source156.dtor_value;
        DAST._IExpression _3478_value = _3477___mcc_h28;
        DAST._IExpression _3479_index = _3476___mcc_h27;
        DAST._IExpression _3480_expr = _3475___mcc_h26;
        {
          RAST._IExpr _3481_exprR;
          DCOMP._IOwnership _3482___v103;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3483_exprIdents;
          RAST._IExpr _out1336;
          DCOMP._IOwnership _out1337;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1338;
          (this).GenExpr(_3480_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1336, out _out1337, out _out1338);
          _3481_exprR = _out1336;
          _3482___v103 = _out1337;
          _3483_exprIdents = _out1338;
          RAST._IExpr _3484_indexR;
          DCOMP._IOwnership _3485_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3486_indexIdents;
          RAST._IExpr _out1339;
          DCOMP._IOwnership _out1340;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1341;
          (this).GenExpr(_3479_index, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1339, out _out1340, out _out1341);
          _3484_indexR = _out1339;
          _3485_indexOwnership = _out1340;
          _3486_indexIdents = _out1341;
          RAST._IExpr _3487_valueR;
          DCOMP._IOwnership _3488_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3489_valueIdents;
          RAST._IExpr _out1342;
          DCOMP._IOwnership _out1343;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1344;
          (this).GenExpr(_3478_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1342, out _out1343, out _out1344);
          _3487_valueR = _out1342;
          _3488_valueOwnership = _out1343;
          _3489_valueIdents = _out1344;
          r = ((_3481_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_3484_indexR, _3487_valueR));
          RAST._IExpr _out1345;
          DCOMP._IOwnership _out1346;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1345, out _out1346);
          r = _out1345;
          resultingOwnership = _out1346;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3483_exprIdents, _3486_indexIdents), _3489_valueIdents);
          return ;
        }
      } else if (_source156.is_MapUpdate) {
        DAST._IExpression _3490___mcc_h29 = _source156.dtor_expr;
        DAST._IExpression _3491___mcc_h30 = _source156.dtor_indexExpr;
        DAST._IExpression _3492___mcc_h31 = _source156.dtor_value;
        DAST._IExpression _3493_value = _3492___mcc_h31;
        DAST._IExpression _3494_index = _3491___mcc_h30;
        DAST._IExpression _3495_expr = _3490___mcc_h29;
        {
          RAST._IExpr _3496_exprR;
          DCOMP._IOwnership _3497___v104;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3498_exprIdents;
          RAST._IExpr _out1347;
          DCOMP._IOwnership _out1348;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1349;
          (this).GenExpr(_3495_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1347, out _out1348, out _out1349);
          _3496_exprR = _out1347;
          _3497___v104 = _out1348;
          _3498_exprIdents = _out1349;
          RAST._IExpr _3499_indexR;
          DCOMP._IOwnership _3500_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3501_indexIdents;
          RAST._IExpr _out1350;
          DCOMP._IOwnership _out1351;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1352;
          (this).GenExpr(_3494_index, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1350, out _out1351, out _out1352);
          _3499_indexR = _out1350;
          _3500_indexOwnership = _out1351;
          _3501_indexIdents = _out1352;
          RAST._IExpr _3502_valueR;
          DCOMP._IOwnership _3503_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3504_valueIdents;
          RAST._IExpr _out1353;
          DCOMP._IOwnership _out1354;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1355;
          (this).GenExpr(_3493_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1353, out _out1354, out _out1355);
          _3502_valueR = _out1353;
          _3503_valueOwnership = _out1354;
          _3504_valueIdents = _out1355;
          r = ((_3496_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_3499_indexR, _3502_valueR));
          RAST._IExpr _out1356;
          DCOMP._IOwnership _out1357;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1356, out _out1357);
          r = _out1356;
          resultingOwnership = _out1357;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3498_exprIdents, _3501_indexIdents), _3504_valueIdents);
          return ;
        }
      } else if (_source156.is_SetBuilder) {
        DAST._IType _3505___mcc_h32 = _source156.dtor_elemType;
        DAST._IType _3506_elemType = _3505___mcc_h32;
        {
          RAST._IType _3507_eType;
          RAST._IType _out1358;
          _out1358 = (this).GenType(_3506_elemType, false, false);
          _3507_eType = _out1358;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::SetBuilder::<"), (_3507_eType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::new()")));
          RAST._IExpr _out1359;
          DCOMP._IOwnership _out1360;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1359, out _out1360);
          r = _out1359;
          resultingOwnership = _out1360;
          return ;
        }
      } else if (_source156.is_ToMultiset) {
        DAST._IExpression _3508___mcc_h33 = _source156.dtor_ToMultiset_a0;
        DAST._IExpression _3509_expr = _3508___mcc_h33;
        {
          RAST._IExpr _3510_recursiveGen;
          DCOMP._IOwnership _3511___v100;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3512_recIdents;
          RAST._IExpr _out1361;
          DCOMP._IOwnership _out1362;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1363;
          (this).GenExpr(_3509_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1361, out _out1362, out _out1363);
          _3510_recursiveGen = _out1361;
          _3511___v100 = _out1362;
          _3512_recIdents = _out1363;
          r = ((_3510_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          readIdents = _3512_recIdents;
          RAST._IExpr _out1364;
          DCOMP._IOwnership _out1365;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1364, out _out1365);
          r = _out1364;
          resultingOwnership = _out1365;
          return ;
        }
      } else if (_source156.is_This) {
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source157 = selfIdent;
          if (_source157.is_None) {
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
            Dafny.ISequence<Dafny.Rune> _3513___mcc_h273 = _source157.dtor_value;
            Dafny.ISequence<Dafny.Rune> _3514_id = _3513___mcc_h273;
            {
              r = RAST.Expr.create_RawExpr(_3514_id);
              if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                r = RAST.__default.Clone(r);
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                if (!(_3514_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.Borrow(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              } else {
                if (!(_3514_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.BorrowMut(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3514_id);
            }
          }
          return ;
        }
      } else if (_source156.is_Ite) {
        DAST._IExpression _3515___mcc_h34 = _source156.dtor_cond;
        DAST._IExpression _3516___mcc_h35 = _source156.dtor_thn;
        DAST._IExpression _3517___mcc_h36 = _source156.dtor_els;
        DAST._IExpression _3518_f = _3517___mcc_h36;
        DAST._IExpression _3519_t = _3516___mcc_h35;
        DAST._IExpression _3520_cond = _3515___mcc_h34;
        {
          RAST._IExpr _3521_cond;
          DCOMP._IOwnership _3522___v105;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3523_recIdentsCond;
          RAST._IExpr _out1368;
          DCOMP._IOwnership _out1369;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1370;
          (this).GenExpr(_3520_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1368, out _out1369, out _out1370);
          _3521_cond = _out1368;
          _3522___v105 = _out1369;
          _3523_recIdentsCond = _out1370;
          Dafny.ISequence<Dafny.Rune> _3524_condString;
          _3524_condString = (_3521_cond)._ToString(DCOMP.__default.IND);
          RAST._IExpr _3525___v106;
          DCOMP._IOwnership _3526_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3527___v107;
          RAST._IExpr _out1371;
          DCOMP._IOwnership _out1372;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1373;
          (this).GenExpr(_3519_t, selfIdent, @params, expectedOwnership, out _out1371, out _out1372, out _out1373);
          _3525___v106 = _out1371;
          _3526_tHasToBeOwned = _out1372;
          _3527___v107 = _out1373;
          RAST._IExpr _3528_fExpr;
          DCOMP._IOwnership _3529_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3530_recIdentsF;
          RAST._IExpr _out1374;
          DCOMP._IOwnership _out1375;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1376;
          (this).GenExpr(_3518_f, selfIdent, @params, _3526_tHasToBeOwned, out _out1374, out _out1375, out _out1376);
          _3528_fExpr = _out1374;
          _3529_fOwned = _out1375;
          _3530_recIdentsF = _out1376;
          Dafny.ISequence<Dafny.Rune> _3531_fString;
          _3531_fString = (_3528_fExpr)._ToString(DCOMP.__default.IND);
          RAST._IExpr _3532_tExpr;
          DCOMP._IOwnership _3533___v108;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3534_recIdentsT;
          RAST._IExpr _out1377;
          DCOMP._IOwnership _out1378;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1379;
          (this).GenExpr(_3519_t, selfIdent, @params, _3529_fOwned, out _out1377, out _out1378, out _out1379);
          _3532_tExpr = _out1377;
          _3533___v108 = _out1378;
          _3534_recIdentsT = _out1379;
          Dafny.ISequence<Dafny.Rune> _3535_tString;
          _3535_tString = (_3532_tExpr)._ToString(DCOMP.__default.IND);
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _3524_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _3535_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _3531_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
          RAST._IExpr _out1380;
          DCOMP._IOwnership _out1381;
          DCOMP.COMP.FromOwnership(r, _3529_fOwned, expectedOwnership, out _out1380, out _out1381);
          r = _out1380;
          resultingOwnership = _out1381;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3523_recIdentsCond, _3534_recIdentsT), _3530_recIdentsF);
          return ;
        }
      } else if (_source156.is_UnOp) {
        DAST._IUnaryOp _3536___mcc_h37 = _source156.dtor_unOp;
        DAST._IExpression _3537___mcc_h38 = _source156.dtor_expr;
        DAST.Format._IUnaryOpFormat _3538___mcc_h39 = _source156.dtor_format1;
        DAST._IUnaryOp _source158 = _3536___mcc_h37;
        if (_source158.is_Not) {
          DAST.Format._IUnaryOpFormat _3539_format = _3538___mcc_h39;
          DAST._IExpression _3540_e = _3537___mcc_h38;
          {
            RAST._IExpr _3541_recursiveGen;
            DCOMP._IOwnership _3542___v109;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3543_recIdents;
            RAST._IExpr _out1382;
            DCOMP._IOwnership _out1383;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1384;
            (this).GenExpr(_3540_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1382, out _out1383, out _out1384);
            _3541_recursiveGen = _out1382;
            _3542___v109 = _out1383;
            _3543_recIdents = _out1384;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _3541_recursiveGen, _3539_format);
            RAST._IExpr _out1385;
            DCOMP._IOwnership _out1386;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1385, out _out1386);
            r = _out1385;
            resultingOwnership = _out1386;
            readIdents = _3543_recIdents;
            return ;
          }
        } else if (_source158.is_BitwiseNot) {
          DAST.Format._IUnaryOpFormat _3544_format = _3538___mcc_h39;
          DAST._IExpression _3545_e = _3537___mcc_h38;
          {
            RAST._IExpr _3546_recursiveGen;
            DCOMP._IOwnership _3547___v110;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3548_recIdents;
            RAST._IExpr _out1387;
            DCOMP._IOwnership _out1388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1389;
            (this).GenExpr(_3545_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1387, out _out1388, out _out1389);
            _3546_recursiveGen = _out1387;
            _3547___v110 = _out1388;
            _3548_recIdents = _out1389;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _3546_recursiveGen, _3544_format);
            RAST._IExpr _out1390;
            DCOMP._IOwnership _out1391;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1390, out _out1391);
            r = _out1390;
            resultingOwnership = _out1391;
            readIdents = _3548_recIdents;
            return ;
          }
        } else {
          DAST.Format._IUnaryOpFormat _3549_format = _3538___mcc_h39;
          DAST._IExpression _3550_e = _3537___mcc_h38;
          {
            RAST._IExpr _3551_recursiveGen;
            DCOMP._IOwnership _3552_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3553_recIdents;
            RAST._IExpr _out1392;
            DCOMP._IOwnership _out1393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1394;
            (this).GenExpr(_3550_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1392, out _out1393, out _out1394);
            _3551_recursiveGen = _out1392;
            _3552_recOwned = _out1393;
            _3553_recIdents = _out1394;
            r = ((_3551_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1395;
            DCOMP._IOwnership _out1396;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1395, out _out1396);
            r = _out1395;
            resultingOwnership = _out1396;
            readIdents = _3553_recIdents;
            return ;
          }
        }
      } else if (_source156.is_BinOp) {
        DAST._IBinOp _3554___mcc_h40 = _source156.dtor_op;
        DAST._IExpression _3555___mcc_h41 = _source156.dtor_left;
        DAST._IExpression _3556___mcc_h42 = _source156.dtor_right;
        DAST.Format._IBinaryOpFormat _3557___mcc_h43 = _source156.dtor_format2;
        RAST._IExpr _out1397;
        DCOMP._IOwnership _out1398;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1399;
        (this).GenExprBinary(e, selfIdent, @params, expectedOwnership, out _out1397, out _out1398, out _out1399);
        r = _out1397;
        resultingOwnership = _out1398;
        readIdents = _out1399;
      } else if (_source156.is_ArrayLen) {
        DAST._IExpression _3558___mcc_h44 = _source156.dtor_expr;
        BigInteger _3559___mcc_h45 = _source156.dtor_dim;
        BigInteger _3560_dim = _3559___mcc_h45;
        DAST._IExpression _3561_expr = _3558___mcc_h44;
        {
          RAST._IExpr _3562_recursiveGen;
          DCOMP._IOwnership _3563___v115;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3564_recIdents;
          RAST._IExpr _out1400;
          DCOMP._IOwnership _out1401;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1402;
          (this).GenExpr(_3561_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1400, out _out1401, out _out1402);
          _3562_recursiveGen = _out1400;
          _3563___v115 = _out1401;
          _3564_recIdents = _out1402;
          if ((_3560_dim).Sign == 0) {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_3562_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
          } else {
            Dafny.ISequence<Dafny.Rune> _3565_s;
            _3565_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
            BigInteger _3566_i;
            _3566_i = BigInteger.One;
            while ((_3566_i) < (_3560_dim)) {
              _3565_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _3565_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
              _3566_i = (_3566_i) + (BigInteger.One);
            }
            r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_3562_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _3565_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
          }
          RAST._IExpr _out1403;
          DCOMP._IOwnership _out1404;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1403, out _out1404);
          r = _out1403;
          resultingOwnership = _out1404;
          readIdents = _3564_recIdents;
          return ;
        }
      } else if (_source156.is_MapKeys) {
        DAST._IExpression _3567___mcc_h46 = _source156.dtor_expr;
        DAST._IExpression _3568_expr = _3567___mcc_h46;
        {
          RAST._IExpr _3569_recursiveGen;
          DCOMP._IOwnership _3570___v116;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3571_recIdents;
          RAST._IExpr _out1405;
          DCOMP._IOwnership _out1406;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1407;
          (this).GenExpr(_3568_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1405, out _out1406, out _out1407);
          _3569_recursiveGen = _out1405;
          _3570___v116 = _out1406;
          _3571_recIdents = _out1407;
          readIdents = _3571_recIdents;
          r = RAST.Expr.create_Call((_3569_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1408;
          DCOMP._IOwnership _out1409;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1408, out _out1409);
          r = _out1408;
          resultingOwnership = _out1409;
          return ;
        }
      } else if (_source156.is_MapValues) {
        DAST._IExpression _3572___mcc_h47 = _source156.dtor_expr;
        DAST._IExpression _3573_expr = _3572___mcc_h47;
        {
          RAST._IExpr _3574_recursiveGen;
          DCOMP._IOwnership _3575___v117;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3576_recIdents;
          RAST._IExpr _out1410;
          DCOMP._IOwnership _out1411;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1412;
          (this).GenExpr(_3573_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1410, out _out1411, out _out1412);
          _3574_recursiveGen = _out1410;
          _3575___v117 = _out1411;
          _3576_recIdents = _out1412;
          readIdents = _3576_recIdents;
          r = RAST.Expr.create_Call((_3574_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1413;
          DCOMP._IOwnership _out1414;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1413, out _out1414);
          r = _out1413;
          resultingOwnership = _out1414;
          return ;
        }
      } else if (_source156.is_Select) {
        DAST._IExpression _3577___mcc_h48 = _source156.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _3578___mcc_h49 = _source156.dtor_field;
        bool _3579___mcc_h50 = _source156.dtor_isConstant;
        bool _3580___mcc_h51 = _source156.dtor_onDatatype;
        DAST._IExpression _source159 = _3577___mcc_h48;
        if (_source159.is_Literal) {
          DAST._ILiteral _3581___mcc_h52 = _source159.dtor_Literal_a0;
          bool _3582_isDatatype = _3580___mcc_h51;
          bool _3583_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3584_field = _3578___mcc_h49;
          DAST._IExpression _3585_on = _3577___mcc_h48;
          {
            RAST._IExpr _3586_onExpr;
            DCOMP._IOwnership _3587_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3588_recIdents;
            RAST._IExpr _out1415;
            DCOMP._IOwnership _out1416;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1417;
            (this).GenExpr(_3585_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1415, out _out1416, out _out1417);
            _3586_onExpr = _out1415;
            _3587_onOwned = _out1416;
            _3588_recIdents = _out1417;
            if ((_3582_isDatatype) || (_3583_isConstant)) {
              r = RAST.Expr.create_Call((_3586_onExpr).Sel(DCOMP.__default.escapeIdent(_3584_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1418;
              DCOMP._IOwnership _out1419;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1418, out _out1419);
              r = _out1418;
              resultingOwnership = _out1419;
            } else {
              Dafny.ISequence<Dafny.Rune> _3589_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3589_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3586_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3584_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1420;
              DCOMP._IOwnership _out1421;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3589_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1420, out _out1421);
              r = _out1420;
              resultingOwnership = _out1421;
            }
            readIdents = _3588_recIdents;
            return ;
          }
        } else if (_source159.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _3590___mcc_h54 = _source159.dtor_Ident_a0;
          bool _3591_isDatatype = _3580___mcc_h51;
          bool _3592_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3593_field = _3578___mcc_h49;
          DAST._IExpression _3594_on = _3577___mcc_h48;
          {
            RAST._IExpr _3595_onExpr;
            DCOMP._IOwnership _3596_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3597_recIdents;
            RAST._IExpr _out1422;
            DCOMP._IOwnership _out1423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1424;
            (this).GenExpr(_3594_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1422, out _out1423, out _out1424);
            _3595_onExpr = _out1422;
            _3596_onOwned = _out1423;
            _3597_recIdents = _out1424;
            if ((_3591_isDatatype) || (_3592_isConstant)) {
              r = RAST.Expr.create_Call((_3595_onExpr).Sel(DCOMP.__default.escapeIdent(_3593_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1425;
              DCOMP._IOwnership _out1426;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1425, out _out1426);
              r = _out1425;
              resultingOwnership = _out1426;
            } else {
              Dafny.ISequence<Dafny.Rune> _3598_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3598_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3595_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3593_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1427;
              DCOMP._IOwnership _out1428;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3598_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1427, out _out1428);
              r = _out1427;
              resultingOwnership = _out1428;
            }
            readIdents = _3597_recIdents;
            return ;
          }
        } else if (_source159.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3599___mcc_h56 = _source159.dtor_Companion_a0;
          bool _3600_isDatatype = _3580___mcc_h51;
          bool _3601_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3602_field = _3578___mcc_h49;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3603_c = _3599___mcc_h56;
          {
            RAST._IExpr _3604_onExpr;
            DCOMP._IOwnership _3605_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3606_recIdents;
            RAST._IExpr _out1429;
            DCOMP._IOwnership _out1430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1431;
            (this).GenExpr(DAST.Expression.create_Companion(_3603_c), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1429, out _out1430, out _out1431);
            _3604_onExpr = _out1429;
            _3605_onOwned = _out1430;
            _3606_recIdents = _out1431;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_3604_onExpr)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_3602_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")));
            RAST._IExpr _out1432;
            DCOMP._IOwnership _out1433;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1432, out _out1433);
            r = _out1432;
            resultingOwnership = _out1433;
            readIdents = _3606_recIdents;
            return ;
          }
        } else if (_source159.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _3607___mcc_h58 = _source159.dtor_Tuple_a0;
          bool _3608_isDatatype = _3580___mcc_h51;
          bool _3609_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3610_field = _3578___mcc_h49;
          DAST._IExpression _3611_on = _3577___mcc_h48;
          {
            RAST._IExpr _3612_onExpr;
            DCOMP._IOwnership _3613_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3614_recIdents;
            RAST._IExpr _out1434;
            DCOMP._IOwnership _out1435;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1436;
            (this).GenExpr(_3611_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1434, out _out1435, out _out1436);
            _3612_onExpr = _out1434;
            _3613_onOwned = _out1435;
            _3614_recIdents = _out1436;
            if ((_3608_isDatatype) || (_3609_isConstant)) {
              r = RAST.Expr.create_Call((_3612_onExpr).Sel(DCOMP.__default.escapeIdent(_3610_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1437;
              DCOMP._IOwnership _out1438;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1437, out _out1438);
              r = _out1437;
              resultingOwnership = _out1438;
            } else {
              Dafny.ISequence<Dafny.Rune> _3615_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3615_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3612_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3610_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1439;
              DCOMP._IOwnership _out1440;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3615_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1439, out _out1440);
              r = _out1439;
              resultingOwnership = _out1440;
            }
            readIdents = _3614_recIdents;
            return ;
          }
        } else if (_source159.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3616___mcc_h60 = _source159.dtor_path;
          Dafny.ISequence<DAST._IType> _3617___mcc_h61 = _source159.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _3618___mcc_h62 = _source159.dtor_args;
          bool _3619_isDatatype = _3580___mcc_h51;
          bool _3620_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3621_field = _3578___mcc_h49;
          DAST._IExpression _3622_on = _3577___mcc_h48;
          {
            RAST._IExpr _3623_onExpr;
            DCOMP._IOwnership _3624_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3625_recIdents;
            RAST._IExpr _out1441;
            DCOMP._IOwnership _out1442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1443;
            (this).GenExpr(_3622_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1441, out _out1442, out _out1443);
            _3623_onExpr = _out1441;
            _3624_onOwned = _out1442;
            _3625_recIdents = _out1443;
            if ((_3619_isDatatype) || (_3620_isConstant)) {
              r = RAST.Expr.create_Call((_3623_onExpr).Sel(DCOMP.__default.escapeIdent(_3621_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1444;
              DCOMP._IOwnership _out1445;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1444, out _out1445);
              r = _out1444;
              resultingOwnership = _out1445;
            } else {
              Dafny.ISequence<Dafny.Rune> _3626_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3626_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3623_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3621_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1446;
              DCOMP._IOwnership _out1447;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3626_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1446, out _out1447);
              r = _out1446;
              resultingOwnership = _out1447;
            }
            readIdents = _3625_recIdents;
            return ;
          }
        } else if (_source159.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _3627___mcc_h66 = _source159.dtor_dims;
          DAST._IType _3628___mcc_h67 = _source159.dtor_typ;
          bool _3629_isDatatype = _3580___mcc_h51;
          bool _3630_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3631_field = _3578___mcc_h49;
          DAST._IExpression _3632_on = _3577___mcc_h48;
          {
            RAST._IExpr _3633_onExpr;
            DCOMP._IOwnership _3634_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3635_recIdents;
            RAST._IExpr _out1448;
            DCOMP._IOwnership _out1449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1450;
            (this).GenExpr(_3632_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1448, out _out1449, out _out1450);
            _3633_onExpr = _out1448;
            _3634_onOwned = _out1449;
            _3635_recIdents = _out1450;
            if ((_3629_isDatatype) || (_3630_isConstant)) {
              r = RAST.Expr.create_Call((_3633_onExpr).Sel(DCOMP.__default.escapeIdent(_3631_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1451;
              DCOMP._IOwnership _out1452;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1451, out _out1452);
              r = _out1451;
              resultingOwnership = _out1452;
            } else {
              Dafny.ISequence<Dafny.Rune> _3636_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3636_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3633_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3631_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1453;
              DCOMP._IOwnership _out1454;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3636_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1453, out _out1454);
              r = _out1453;
              resultingOwnership = _out1454;
            }
            readIdents = _3635_recIdents;
            return ;
          }
        } else if (_source159.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3637___mcc_h70 = _source159.dtor_path;
          Dafny.ISequence<DAST._IType> _3638___mcc_h71 = _source159.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _3639___mcc_h72 = _source159.dtor_variant;
          bool _3640___mcc_h73 = _source159.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3641___mcc_h74 = _source159.dtor_contents;
          bool _3642_isDatatype = _3580___mcc_h51;
          bool _3643_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3644_field = _3578___mcc_h49;
          DAST._IExpression _3645_on = _3577___mcc_h48;
          {
            RAST._IExpr _3646_onExpr;
            DCOMP._IOwnership _3647_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3648_recIdents;
            RAST._IExpr _out1455;
            DCOMP._IOwnership _out1456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1457;
            (this).GenExpr(_3645_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1455, out _out1456, out _out1457);
            _3646_onExpr = _out1455;
            _3647_onOwned = _out1456;
            _3648_recIdents = _out1457;
            if ((_3642_isDatatype) || (_3643_isConstant)) {
              r = RAST.Expr.create_Call((_3646_onExpr).Sel(DCOMP.__default.escapeIdent(_3644_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1458;
              DCOMP._IOwnership _out1459;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1458, out _out1459);
              r = _out1458;
              resultingOwnership = _out1459;
            } else {
              Dafny.ISequence<Dafny.Rune> _3649_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3649_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3646_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3644_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1460;
              DCOMP._IOwnership _out1461;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3649_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1460, out _out1461);
              r = _out1460;
              resultingOwnership = _out1461;
            }
            readIdents = _3648_recIdents;
            return ;
          }
        } else if (_source159.is_Convert) {
          DAST._IExpression _3650___mcc_h80 = _source159.dtor_value;
          DAST._IType _3651___mcc_h81 = _source159.dtor_from;
          DAST._IType _3652___mcc_h82 = _source159.dtor_typ;
          bool _3653_isDatatype = _3580___mcc_h51;
          bool _3654_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3655_field = _3578___mcc_h49;
          DAST._IExpression _3656_on = _3577___mcc_h48;
          {
            RAST._IExpr _3657_onExpr;
            DCOMP._IOwnership _3658_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3659_recIdents;
            RAST._IExpr _out1462;
            DCOMP._IOwnership _out1463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1464;
            (this).GenExpr(_3656_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1462, out _out1463, out _out1464);
            _3657_onExpr = _out1462;
            _3658_onOwned = _out1463;
            _3659_recIdents = _out1464;
            if ((_3653_isDatatype) || (_3654_isConstant)) {
              r = RAST.Expr.create_Call((_3657_onExpr).Sel(DCOMP.__default.escapeIdent(_3655_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1465;
              DCOMP._IOwnership _out1466;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1465, out _out1466);
              r = _out1465;
              resultingOwnership = _out1466;
            } else {
              Dafny.ISequence<Dafny.Rune> _3660_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3660_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3657_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3655_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1467;
              DCOMP._IOwnership _out1468;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3660_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1467, out _out1468);
              r = _out1467;
              resultingOwnership = _out1468;
            }
            readIdents = _3659_recIdents;
            return ;
          }
        } else if (_source159.is_SeqConstruct) {
          DAST._IExpression _3661___mcc_h86 = _source159.dtor_length;
          DAST._IExpression _3662___mcc_h87 = _source159.dtor_elem;
          bool _3663_isDatatype = _3580___mcc_h51;
          bool _3664_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3665_field = _3578___mcc_h49;
          DAST._IExpression _3666_on = _3577___mcc_h48;
          {
            RAST._IExpr _3667_onExpr;
            DCOMP._IOwnership _3668_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3669_recIdents;
            RAST._IExpr _out1469;
            DCOMP._IOwnership _out1470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1471;
            (this).GenExpr(_3666_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1469, out _out1470, out _out1471);
            _3667_onExpr = _out1469;
            _3668_onOwned = _out1470;
            _3669_recIdents = _out1471;
            if ((_3663_isDatatype) || (_3664_isConstant)) {
              r = RAST.Expr.create_Call((_3667_onExpr).Sel(DCOMP.__default.escapeIdent(_3665_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1472;
              DCOMP._IOwnership _out1473;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1472, out _out1473);
              r = _out1472;
              resultingOwnership = _out1473;
            } else {
              Dafny.ISequence<Dafny.Rune> _3670_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3670_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3667_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3665_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1474;
              DCOMP._IOwnership _out1475;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3670_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1474, out _out1475);
              r = _out1474;
              resultingOwnership = _out1475;
            }
            readIdents = _3669_recIdents;
            return ;
          }
        } else if (_source159.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _3671___mcc_h90 = _source159.dtor_elements;
          DAST._IType _3672___mcc_h91 = _source159.dtor_typ;
          bool _3673_isDatatype = _3580___mcc_h51;
          bool _3674_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3675_field = _3578___mcc_h49;
          DAST._IExpression _3676_on = _3577___mcc_h48;
          {
            RAST._IExpr _3677_onExpr;
            DCOMP._IOwnership _3678_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3679_recIdents;
            RAST._IExpr _out1476;
            DCOMP._IOwnership _out1477;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1478;
            (this).GenExpr(_3676_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1476, out _out1477, out _out1478);
            _3677_onExpr = _out1476;
            _3678_onOwned = _out1477;
            _3679_recIdents = _out1478;
            if ((_3673_isDatatype) || (_3674_isConstant)) {
              r = RAST.Expr.create_Call((_3677_onExpr).Sel(DCOMP.__default.escapeIdent(_3675_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1479;
              DCOMP._IOwnership _out1480;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1479, out _out1480);
              r = _out1479;
              resultingOwnership = _out1480;
            } else {
              Dafny.ISequence<Dafny.Rune> _3680_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3680_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3677_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3675_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1481;
              DCOMP._IOwnership _out1482;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3680_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1481, out _out1482);
              r = _out1481;
              resultingOwnership = _out1482;
            }
            readIdents = _3679_recIdents;
            return ;
          }
        } else if (_source159.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _3681___mcc_h94 = _source159.dtor_elements;
          bool _3682_isDatatype = _3580___mcc_h51;
          bool _3683_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3684_field = _3578___mcc_h49;
          DAST._IExpression _3685_on = _3577___mcc_h48;
          {
            RAST._IExpr _3686_onExpr;
            DCOMP._IOwnership _3687_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3688_recIdents;
            RAST._IExpr _out1483;
            DCOMP._IOwnership _out1484;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1485;
            (this).GenExpr(_3685_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1483, out _out1484, out _out1485);
            _3686_onExpr = _out1483;
            _3687_onOwned = _out1484;
            _3688_recIdents = _out1485;
            if ((_3682_isDatatype) || (_3683_isConstant)) {
              r = RAST.Expr.create_Call((_3686_onExpr).Sel(DCOMP.__default.escapeIdent(_3684_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1486;
              DCOMP._IOwnership _out1487;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1486, out _out1487);
              r = _out1486;
              resultingOwnership = _out1487;
            } else {
              Dafny.ISequence<Dafny.Rune> _3689_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3689_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3686_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3684_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1488;
              DCOMP._IOwnership _out1489;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3689_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1488, out _out1489);
              r = _out1488;
              resultingOwnership = _out1489;
            }
            readIdents = _3688_recIdents;
            return ;
          }
        } else if (_source159.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _3690___mcc_h96 = _source159.dtor_elements;
          bool _3691_isDatatype = _3580___mcc_h51;
          bool _3692_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3693_field = _3578___mcc_h49;
          DAST._IExpression _3694_on = _3577___mcc_h48;
          {
            RAST._IExpr _3695_onExpr;
            DCOMP._IOwnership _3696_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3697_recIdents;
            RAST._IExpr _out1490;
            DCOMP._IOwnership _out1491;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1492;
            (this).GenExpr(_3694_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1490, out _out1491, out _out1492);
            _3695_onExpr = _out1490;
            _3696_onOwned = _out1491;
            _3697_recIdents = _out1492;
            if ((_3691_isDatatype) || (_3692_isConstant)) {
              r = RAST.Expr.create_Call((_3695_onExpr).Sel(DCOMP.__default.escapeIdent(_3693_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1493;
              DCOMP._IOwnership _out1494;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1493, out _out1494);
              r = _out1493;
              resultingOwnership = _out1494;
            } else {
              Dafny.ISequence<Dafny.Rune> _3698_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3698_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3695_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3693_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1495;
              DCOMP._IOwnership _out1496;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3698_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1495, out _out1496);
              r = _out1495;
              resultingOwnership = _out1496;
            }
            readIdents = _3697_recIdents;
            return ;
          }
        } else if (_source159.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3699___mcc_h98 = _source159.dtor_mapElems;
          bool _3700_isDatatype = _3580___mcc_h51;
          bool _3701_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3702_field = _3578___mcc_h49;
          DAST._IExpression _3703_on = _3577___mcc_h48;
          {
            RAST._IExpr _3704_onExpr;
            DCOMP._IOwnership _3705_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3706_recIdents;
            RAST._IExpr _out1497;
            DCOMP._IOwnership _out1498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1499;
            (this).GenExpr(_3703_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1497, out _out1498, out _out1499);
            _3704_onExpr = _out1497;
            _3705_onOwned = _out1498;
            _3706_recIdents = _out1499;
            if ((_3700_isDatatype) || (_3701_isConstant)) {
              r = RAST.Expr.create_Call((_3704_onExpr).Sel(DCOMP.__default.escapeIdent(_3702_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1500;
              DCOMP._IOwnership _out1501;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1500, out _out1501);
              r = _out1500;
              resultingOwnership = _out1501;
            } else {
              Dafny.ISequence<Dafny.Rune> _3707_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3707_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3704_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3702_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1502;
              DCOMP._IOwnership _out1503;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3707_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1502, out _out1503);
              r = _out1502;
              resultingOwnership = _out1503;
            }
            readIdents = _3706_recIdents;
            return ;
          }
        } else if (_source159.is_MapBuilder) {
          DAST._IType _3708___mcc_h100 = _source159.dtor_keyType;
          DAST._IType _3709___mcc_h101 = _source159.dtor_valueType;
          bool _3710_isDatatype = _3580___mcc_h51;
          bool _3711_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3712_field = _3578___mcc_h49;
          DAST._IExpression _3713_on = _3577___mcc_h48;
          {
            RAST._IExpr _3714_onExpr;
            DCOMP._IOwnership _3715_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3716_recIdents;
            RAST._IExpr _out1504;
            DCOMP._IOwnership _out1505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1506;
            (this).GenExpr(_3713_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1504, out _out1505, out _out1506);
            _3714_onExpr = _out1504;
            _3715_onOwned = _out1505;
            _3716_recIdents = _out1506;
            if ((_3710_isDatatype) || (_3711_isConstant)) {
              r = RAST.Expr.create_Call((_3714_onExpr).Sel(DCOMP.__default.escapeIdent(_3712_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1507;
              DCOMP._IOwnership _out1508;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1507, out _out1508);
              r = _out1507;
              resultingOwnership = _out1508;
            } else {
              Dafny.ISequence<Dafny.Rune> _3717_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3717_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3714_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3712_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1509;
              DCOMP._IOwnership _out1510;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3717_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1509, out _out1510);
              r = _out1509;
              resultingOwnership = _out1510;
            }
            readIdents = _3716_recIdents;
            return ;
          }
        } else if (_source159.is_SeqUpdate) {
          DAST._IExpression _3718___mcc_h104 = _source159.dtor_expr;
          DAST._IExpression _3719___mcc_h105 = _source159.dtor_indexExpr;
          DAST._IExpression _3720___mcc_h106 = _source159.dtor_value;
          bool _3721_isDatatype = _3580___mcc_h51;
          bool _3722_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3723_field = _3578___mcc_h49;
          DAST._IExpression _3724_on = _3577___mcc_h48;
          {
            RAST._IExpr _3725_onExpr;
            DCOMP._IOwnership _3726_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3727_recIdents;
            RAST._IExpr _out1511;
            DCOMP._IOwnership _out1512;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1513;
            (this).GenExpr(_3724_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1511, out _out1512, out _out1513);
            _3725_onExpr = _out1511;
            _3726_onOwned = _out1512;
            _3727_recIdents = _out1513;
            if ((_3721_isDatatype) || (_3722_isConstant)) {
              r = RAST.Expr.create_Call((_3725_onExpr).Sel(DCOMP.__default.escapeIdent(_3723_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1514;
              DCOMP._IOwnership _out1515;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1514, out _out1515);
              r = _out1514;
              resultingOwnership = _out1515;
            } else {
              Dafny.ISequence<Dafny.Rune> _3728_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3728_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3725_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3723_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1516;
              DCOMP._IOwnership _out1517;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3728_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1516, out _out1517);
              r = _out1516;
              resultingOwnership = _out1517;
            }
            readIdents = _3727_recIdents;
            return ;
          }
        } else if (_source159.is_MapUpdate) {
          DAST._IExpression _3729___mcc_h110 = _source159.dtor_expr;
          DAST._IExpression _3730___mcc_h111 = _source159.dtor_indexExpr;
          DAST._IExpression _3731___mcc_h112 = _source159.dtor_value;
          bool _3732_isDatatype = _3580___mcc_h51;
          bool _3733_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3734_field = _3578___mcc_h49;
          DAST._IExpression _3735_on = _3577___mcc_h48;
          {
            RAST._IExpr _3736_onExpr;
            DCOMP._IOwnership _3737_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3738_recIdents;
            RAST._IExpr _out1518;
            DCOMP._IOwnership _out1519;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1520;
            (this).GenExpr(_3735_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1518, out _out1519, out _out1520);
            _3736_onExpr = _out1518;
            _3737_onOwned = _out1519;
            _3738_recIdents = _out1520;
            if ((_3732_isDatatype) || (_3733_isConstant)) {
              r = RAST.Expr.create_Call((_3736_onExpr).Sel(DCOMP.__default.escapeIdent(_3734_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1521;
              DCOMP._IOwnership _out1522;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1521, out _out1522);
              r = _out1521;
              resultingOwnership = _out1522;
            } else {
              Dafny.ISequence<Dafny.Rune> _3739_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3739_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3736_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3734_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1523;
              DCOMP._IOwnership _out1524;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3739_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1523, out _out1524);
              r = _out1523;
              resultingOwnership = _out1524;
            }
            readIdents = _3738_recIdents;
            return ;
          }
        } else if (_source159.is_SetBuilder) {
          DAST._IType _3740___mcc_h116 = _source159.dtor_elemType;
          bool _3741_isDatatype = _3580___mcc_h51;
          bool _3742_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3743_field = _3578___mcc_h49;
          DAST._IExpression _3744_on = _3577___mcc_h48;
          {
            RAST._IExpr _3745_onExpr;
            DCOMP._IOwnership _3746_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3747_recIdents;
            RAST._IExpr _out1525;
            DCOMP._IOwnership _out1526;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1527;
            (this).GenExpr(_3744_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1525, out _out1526, out _out1527);
            _3745_onExpr = _out1525;
            _3746_onOwned = _out1526;
            _3747_recIdents = _out1527;
            if ((_3741_isDatatype) || (_3742_isConstant)) {
              r = RAST.Expr.create_Call((_3745_onExpr).Sel(DCOMP.__default.escapeIdent(_3743_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1528;
              DCOMP._IOwnership _out1529;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1528, out _out1529);
              r = _out1528;
              resultingOwnership = _out1529;
            } else {
              Dafny.ISequence<Dafny.Rune> _3748_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3748_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3745_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3743_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1530;
              DCOMP._IOwnership _out1531;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3748_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1530, out _out1531);
              r = _out1530;
              resultingOwnership = _out1531;
            }
            readIdents = _3747_recIdents;
            return ;
          }
        } else if (_source159.is_ToMultiset) {
          DAST._IExpression _3749___mcc_h118 = _source159.dtor_ToMultiset_a0;
          bool _3750_isDatatype = _3580___mcc_h51;
          bool _3751_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3752_field = _3578___mcc_h49;
          DAST._IExpression _3753_on = _3577___mcc_h48;
          {
            RAST._IExpr _3754_onExpr;
            DCOMP._IOwnership _3755_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3756_recIdents;
            RAST._IExpr _out1532;
            DCOMP._IOwnership _out1533;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1534;
            (this).GenExpr(_3753_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1532, out _out1533, out _out1534);
            _3754_onExpr = _out1532;
            _3755_onOwned = _out1533;
            _3756_recIdents = _out1534;
            if ((_3750_isDatatype) || (_3751_isConstant)) {
              r = RAST.Expr.create_Call((_3754_onExpr).Sel(DCOMP.__default.escapeIdent(_3752_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1535;
              DCOMP._IOwnership _out1536;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1535, out _out1536);
              r = _out1535;
              resultingOwnership = _out1536;
            } else {
              Dafny.ISequence<Dafny.Rune> _3757_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3757_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3754_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3752_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1537;
              DCOMP._IOwnership _out1538;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3757_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1537, out _out1538);
              r = _out1537;
              resultingOwnership = _out1538;
            }
            readIdents = _3756_recIdents;
            return ;
          }
        } else if (_source159.is_This) {
          bool _3758_isDatatype = _3580___mcc_h51;
          bool _3759_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3760_field = _3578___mcc_h49;
          DAST._IExpression _3761_on = _3577___mcc_h48;
          {
            RAST._IExpr _3762_onExpr;
            DCOMP._IOwnership _3763_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3764_recIdents;
            RAST._IExpr _out1539;
            DCOMP._IOwnership _out1540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1541;
            (this).GenExpr(_3761_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1539, out _out1540, out _out1541);
            _3762_onExpr = _out1539;
            _3763_onOwned = _out1540;
            _3764_recIdents = _out1541;
            if ((_3758_isDatatype) || (_3759_isConstant)) {
              r = RAST.Expr.create_Call((_3762_onExpr).Sel(DCOMP.__default.escapeIdent(_3760_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1542;
              DCOMP._IOwnership _out1543;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1542, out _out1543);
              r = _out1542;
              resultingOwnership = _out1543;
            } else {
              Dafny.ISequence<Dafny.Rune> _3765_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3765_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3762_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3760_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1544;
              DCOMP._IOwnership _out1545;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3765_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1544, out _out1545);
              r = _out1544;
              resultingOwnership = _out1545;
            }
            readIdents = _3764_recIdents;
            return ;
          }
        } else if (_source159.is_Ite) {
          DAST._IExpression _3766___mcc_h120 = _source159.dtor_cond;
          DAST._IExpression _3767___mcc_h121 = _source159.dtor_thn;
          DAST._IExpression _3768___mcc_h122 = _source159.dtor_els;
          bool _3769_isDatatype = _3580___mcc_h51;
          bool _3770_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3771_field = _3578___mcc_h49;
          DAST._IExpression _3772_on = _3577___mcc_h48;
          {
            RAST._IExpr _3773_onExpr;
            DCOMP._IOwnership _3774_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3775_recIdents;
            RAST._IExpr _out1546;
            DCOMP._IOwnership _out1547;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1548;
            (this).GenExpr(_3772_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1546, out _out1547, out _out1548);
            _3773_onExpr = _out1546;
            _3774_onOwned = _out1547;
            _3775_recIdents = _out1548;
            if ((_3769_isDatatype) || (_3770_isConstant)) {
              r = RAST.Expr.create_Call((_3773_onExpr).Sel(DCOMP.__default.escapeIdent(_3771_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1549;
              DCOMP._IOwnership _out1550;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1549, out _out1550);
              r = _out1549;
              resultingOwnership = _out1550;
            } else {
              Dafny.ISequence<Dafny.Rune> _3776_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3776_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3773_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3771_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1551;
              DCOMP._IOwnership _out1552;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3776_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1551, out _out1552);
              r = _out1551;
              resultingOwnership = _out1552;
            }
            readIdents = _3775_recIdents;
            return ;
          }
        } else if (_source159.is_UnOp) {
          DAST._IUnaryOp _3777___mcc_h126 = _source159.dtor_unOp;
          DAST._IExpression _3778___mcc_h127 = _source159.dtor_expr;
          DAST.Format._IUnaryOpFormat _3779___mcc_h128 = _source159.dtor_format1;
          bool _3780_isDatatype = _3580___mcc_h51;
          bool _3781_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3782_field = _3578___mcc_h49;
          DAST._IExpression _3783_on = _3577___mcc_h48;
          {
            RAST._IExpr _3784_onExpr;
            DCOMP._IOwnership _3785_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3786_recIdents;
            RAST._IExpr _out1553;
            DCOMP._IOwnership _out1554;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1555;
            (this).GenExpr(_3783_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1553, out _out1554, out _out1555);
            _3784_onExpr = _out1553;
            _3785_onOwned = _out1554;
            _3786_recIdents = _out1555;
            if ((_3780_isDatatype) || (_3781_isConstant)) {
              r = RAST.Expr.create_Call((_3784_onExpr).Sel(DCOMP.__default.escapeIdent(_3782_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1556;
              DCOMP._IOwnership _out1557;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1556, out _out1557);
              r = _out1556;
              resultingOwnership = _out1557;
            } else {
              Dafny.ISequence<Dafny.Rune> _3787_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3787_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3784_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3782_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1558;
              DCOMP._IOwnership _out1559;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3787_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1558, out _out1559);
              r = _out1558;
              resultingOwnership = _out1559;
            }
            readIdents = _3786_recIdents;
            return ;
          }
        } else if (_source159.is_BinOp) {
          DAST._IBinOp _3788___mcc_h132 = _source159.dtor_op;
          DAST._IExpression _3789___mcc_h133 = _source159.dtor_left;
          DAST._IExpression _3790___mcc_h134 = _source159.dtor_right;
          DAST.Format._IBinaryOpFormat _3791___mcc_h135 = _source159.dtor_format2;
          bool _3792_isDatatype = _3580___mcc_h51;
          bool _3793_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3794_field = _3578___mcc_h49;
          DAST._IExpression _3795_on = _3577___mcc_h48;
          {
            RAST._IExpr _3796_onExpr;
            DCOMP._IOwnership _3797_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3798_recIdents;
            RAST._IExpr _out1560;
            DCOMP._IOwnership _out1561;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1562;
            (this).GenExpr(_3795_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1560, out _out1561, out _out1562);
            _3796_onExpr = _out1560;
            _3797_onOwned = _out1561;
            _3798_recIdents = _out1562;
            if ((_3792_isDatatype) || (_3793_isConstant)) {
              r = RAST.Expr.create_Call((_3796_onExpr).Sel(DCOMP.__default.escapeIdent(_3794_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1563;
              DCOMP._IOwnership _out1564;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1563, out _out1564);
              r = _out1563;
              resultingOwnership = _out1564;
            } else {
              Dafny.ISequence<Dafny.Rune> _3799_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3799_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3796_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3794_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1565;
              DCOMP._IOwnership _out1566;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3799_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1565, out _out1566);
              r = _out1565;
              resultingOwnership = _out1566;
            }
            readIdents = _3798_recIdents;
            return ;
          }
        } else if (_source159.is_ArrayLen) {
          DAST._IExpression _3800___mcc_h140 = _source159.dtor_expr;
          BigInteger _3801___mcc_h141 = _source159.dtor_dim;
          bool _3802_isDatatype = _3580___mcc_h51;
          bool _3803_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3804_field = _3578___mcc_h49;
          DAST._IExpression _3805_on = _3577___mcc_h48;
          {
            RAST._IExpr _3806_onExpr;
            DCOMP._IOwnership _3807_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3808_recIdents;
            RAST._IExpr _out1567;
            DCOMP._IOwnership _out1568;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1569;
            (this).GenExpr(_3805_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1567, out _out1568, out _out1569);
            _3806_onExpr = _out1567;
            _3807_onOwned = _out1568;
            _3808_recIdents = _out1569;
            if ((_3802_isDatatype) || (_3803_isConstant)) {
              r = RAST.Expr.create_Call((_3806_onExpr).Sel(DCOMP.__default.escapeIdent(_3804_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1570;
              DCOMP._IOwnership _out1571;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1570, out _out1571);
              r = _out1570;
              resultingOwnership = _out1571;
            } else {
              Dafny.ISequence<Dafny.Rune> _3809_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3809_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3806_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3804_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1572;
              DCOMP._IOwnership _out1573;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3809_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1572, out _out1573);
              r = _out1572;
              resultingOwnership = _out1573;
            }
            readIdents = _3808_recIdents;
            return ;
          }
        } else if (_source159.is_MapKeys) {
          DAST._IExpression _3810___mcc_h144 = _source159.dtor_expr;
          bool _3811_isDatatype = _3580___mcc_h51;
          bool _3812_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3813_field = _3578___mcc_h49;
          DAST._IExpression _3814_on = _3577___mcc_h48;
          {
            RAST._IExpr _3815_onExpr;
            DCOMP._IOwnership _3816_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3817_recIdents;
            RAST._IExpr _out1574;
            DCOMP._IOwnership _out1575;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1576;
            (this).GenExpr(_3814_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1574, out _out1575, out _out1576);
            _3815_onExpr = _out1574;
            _3816_onOwned = _out1575;
            _3817_recIdents = _out1576;
            if ((_3811_isDatatype) || (_3812_isConstant)) {
              r = RAST.Expr.create_Call((_3815_onExpr).Sel(DCOMP.__default.escapeIdent(_3813_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1577;
              DCOMP._IOwnership _out1578;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1577, out _out1578);
              r = _out1577;
              resultingOwnership = _out1578;
            } else {
              Dafny.ISequence<Dafny.Rune> _3818_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3818_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3815_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3813_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1579;
              DCOMP._IOwnership _out1580;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3818_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1579, out _out1580);
              r = _out1579;
              resultingOwnership = _out1580;
            }
            readIdents = _3817_recIdents;
            return ;
          }
        } else if (_source159.is_MapValues) {
          DAST._IExpression _3819___mcc_h146 = _source159.dtor_expr;
          bool _3820_isDatatype = _3580___mcc_h51;
          bool _3821_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3822_field = _3578___mcc_h49;
          DAST._IExpression _3823_on = _3577___mcc_h48;
          {
            RAST._IExpr _3824_onExpr;
            DCOMP._IOwnership _3825_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3826_recIdents;
            RAST._IExpr _out1581;
            DCOMP._IOwnership _out1582;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1583;
            (this).GenExpr(_3823_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1581, out _out1582, out _out1583);
            _3824_onExpr = _out1581;
            _3825_onOwned = _out1582;
            _3826_recIdents = _out1583;
            if ((_3820_isDatatype) || (_3821_isConstant)) {
              r = RAST.Expr.create_Call((_3824_onExpr).Sel(DCOMP.__default.escapeIdent(_3822_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1584;
              DCOMP._IOwnership _out1585;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1584, out _out1585);
              r = _out1584;
              resultingOwnership = _out1585;
            } else {
              Dafny.ISequence<Dafny.Rune> _3827_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3827_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3824_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3822_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1586;
              DCOMP._IOwnership _out1587;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3827_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1586, out _out1587);
              r = _out1586;
              resultingOwnership = _out1587;
            }
            readIdents = _3826_recIdents;
            return ;
          }
        } else if (_source159.is_Select) {
          DAST._IExpression _3828___mcc_h148 = _source159.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _3829___mcc_h149 = _source159.dtor_field;
          bool _3830___mcc_h150 = _source159.dtor_isConstant;
          bool _3831___mcc_h151 = _source159.dtor_onDatatype;
          bool _3832_isDatatype = _3580___mcc_h51;
          bool _3833_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3834_field = _3578___mcc_h49;
          DAST._IExpression _3835_on = _3577___mcc_h48;
          {
            RAST._IExpr _3836_onExpr;
            DCOMP._IOwnership _3837_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3838_recIdents;
            RAST._IExpr _out1588;
            DCOMP._IOwnership _out1589;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1590;
            (this).GenExpr(_3835_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1588, out _out1589, out _out1590);
            _3836_onExpr = _out1588;
            _3837_onOwned = _out1589;
            _3838_recIdents = _out1590;
            if ((_3832_isDatatype) || (_3833_isConstant)) {
              r = RAST.Expr.create_Call((_3836_onExpr).Sel(DCOMP.__default.escapeIdent(_3834_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1591;
              DCOMP._IOwnership _out1592;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1591, out _out1592);
              r = _out1591;
              resultingOwnership = _out1592;
            } else {
              Dafny.ISequence<Dafny.Rune> _3839_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3839_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3836_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3834_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1593;
              DCOMP._IOwnership _out1594;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3839_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1593, out _out1594);
              r = _out1593;
              resultingOwnership = _out1594;
            }
            readIdents = _3838_recIdents;
            return ;
          }
        } else if (_source159.is_SelectFn) {
          DAST._IExpression _3840___mcc_h156 = _source159.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _3841___mcc_h157 = _source159.dtor_field;
          bool _3842___mcc_h158 = _source159.dtor_onDatatype;
          bool _3843___mcc_h159 = _source159.dtor_isStatic;
          BigInteger _3844___mcc_h160 = _source159.dtor_arity;
          bool _3845_isDatatype = _3580___mcc_h51;
          bool _3846_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3847_field = _3578___mcc_h49;
          DAST._IExpression _3848_on = _3577___mcc_h48;
          {
            RAST._IExpr _3849_onExpr;
            DCOMP._IOwnership _3850_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3851_recIdents;
            RAST._IExpr _out1595;
            DCOMP._IOwnership _out1596;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1597;
            (this).GenExpr(_3848_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1595, out _out1596, out _out1597);
            _3849_onExpr = _out1595;
            _3850_onOwned = _out1596;
            _3851_recIdents = _out1597;
            if ((_3845_isDatatype) || (_3846_isConstant)) {
              r = RAST.Expr.create_Call((_3849_onExpr).Sel(DCOMP.__default.escapeIdent(_3847_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1598;
              DCOMP._IOwnership _out1599;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1598, out _out1599);
              r = _out1598;
              resultingOwnership = _out1599;
            } else {
              Dafny.ISequence<Dafny.Rune> _3852_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3852_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3849_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3847_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1600;
              DCOMP._IOwnership _out1601;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3852_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1600, out _out1601);
              r = _out1600;
              resultingOwnership = _out1601;
            }
            readIdents = _3851_recIdents;
            return ;
          }
        } else if (_source159.is_Index) {
          DAST._IExpression _3853___mcc_h166 = _source159.dtor_expr;
          DAST._ICollKind _3854___mcc_h167 = _source159.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _3855___mcc_h168 = _source159.dtor_indices;
          bool _3856_isDatatype = _3580___mcc_h51;
          bool _3857_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3858_field = _3578___mcc_h49;
          DAST._IExpression _3859_on = _3577___mcc_h48;
          {
            RAST._IExpr _3860_onExpr;
            DCOMP._IOwnership _3861_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3862_recIdents;
            RAST._IExpr _out1602;
            DCOMP._IOwnership _out1603;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1604;
            (this).GenExpr(_3859_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1602, out _out1603, out _out1604);
            _3860_onExpr = _out1602;
            _3861_onOwned = _out1603;
            _3862_recIdents = _out1604;
            if ((_3856_isDatatype) || (_3857_isConstant)) {
              r = RAST.Expr.create_Call((_3860_onExpr).Sel(DCOMP.__default.escapeIdent(_3858_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1605;
              DCOMP._IOwnership _out1606;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1605, out _out1606);
              r = _out1605;
              resultingOwnership = _out1606;
            } else {
              Dafny.ISequence<Dafny.Rune> _3863_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3863_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3860_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3858_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1607;
              DCOMP._IOwnership _out1608;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3863_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1607, out _out1608);
              r = _out1607;
              resultingOwnership = _out1608;
            }
            readIdents = _3862_recIdents;
            return ;
          }
        } else if (_source159.is_IndexRange) {
          DAST._IExpression _3864___mcc_h172 = _source159.dtor_expr;
          bool _3865___mcc_h173 = _source159.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _3866___mcc_h174 = _source159.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _3867___mcc_h175 = _source159.dtor_high;
          bool _3868_isDatatype = _3580___mcc_h51;
          bool _3869_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3870_field = _3578___mcc_h49;
          DAST._IExpression _3871_on = _3577___mcc_h48;
          {
            RAST._IExpr _3872_onExpr;
            DCOMP._IOwnership _3873_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3874_recIdents;
            RAST._IExpr _out1609;
            DCOMP._IOwnership _out1610;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1611;
            (this).GenExpr(_3871_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1609, out _out1610, out _out1611);
            _3872_onExpr = _out1609;
            _3873_onOwned = _out1610;
            _3874_recIdents = _out1611;
            if ((_3868_isDatatype) || (_3869_isConstant)) {
              r = RAST.Expr.create_Call((_3872_onExpr).Sel(DCOMP.__default.escapeIdent(_3870_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1612;
              DCOMP._IOwnership _out1613;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1612, out _out1613);
              r = _out1612;
              resultingOwnership = _out1613;
            } else {
              Dafny.ISequence<Dafny.Rune> _3875_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3875_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3872_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3870_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1614;
              DCOMP._IOwnership _out1615;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3875_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1614, out _out1615);
              r = _out1614;
              resultingOwnership = _out1615;
            }
            readIdents = _3874_recIdents;
            return ;
          }
        } else if (_source159.is_TupleSelect) {
          DAST._IExpression _3876___mcc_h180 = _source159.dtor_expr;
          BigInteger _3877___mcc_h181 = _source159.dtor_index;
          bool _3878_isDatatype = _3580___mcc_h51;
          bool _3879_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3880_field = _3578___mcc_h49;
          DAST._IExpression _3881_on = _3577___mcc_h48;
          {
            RAST._IExpr _3882_onExpr;
            DCOMP._IOwnership _3883_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3884_recIdents;
            RAST._IExpr _out1616;
            DCOMP._IOwnership _out1617;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1618;
            (this).GenExpr(_3881_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1616, out _out1617, out _out1618);
            _3882_onExpr = _out1616;
            _3883_onOwned = _out1617;
            _3884_recIdents = _out1618;
            if ((_3878_isDatatype) || (_3879_isConstant)) {
              r = RAST.Expr.create_Call((_3882_onExpr).Sel(DCOMP.__default.escapeIdent(_3880_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1619;
              DCOMP._IOwnership _out1620;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1619, out _out1620);
              r = _out1619;
              resultingOwnership = _out1620;
            } else {
              Dafny.ISequence<Dafny.Rune> _3885_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3885_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3882_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3880_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1621;
              DCOMP._IOwnership _out1622;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3885_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1621, out _out1622);
              r = _out1621;
              resultingOwnership = _out1622;
            }
            readIdents = _3884_recIdents;
            return ;
          }
        } else if (_source159.is_Call) {
          DAST._IExpression _3886___mcc_h184 = _source159.dtor_on;
          DAST._ICallName _3887___mcc_h185 = _source159.dtor_callName;
          Dafny.ISequence<DAST._IType> _3888___mcc_h186 = _source159.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _3889___mcc_h187 = _source159.dtor_args;
          bool _3890_isDatatype = _3580___mcc_h51;
          bool _3891_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3892_field = _3578___mcc_h49;
          DAST._IExpression _3893_on = _3577___mcc_h48;
          {
            RAST._IExpr _3894_onExpr;
            DCOMP._IOwnership _3895_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3896_recIdents;
            RAST._IExpr _out1623;
            DCOMP._IOwnership _out1624;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1625;
            (this).GenExpr(_3893_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1623, out _out1624, out _out1625);
            _3894_onExpr = _out1623;
            _3895_onOwned = _out1624;
            _3896_recIdents = _out1625;
            if ((_3890_isDatatype) || (_3891_isConstant)) {
              r = RAST.Expr.create_Call((_3894_onExpr).Sel(DCOMP.__default.escapeIdent(_3892_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1626;
              DCOMP._IOwnership _out1627;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1626, out _out1627);
              r = _out1626;
              resultingOwnership = _out1627;
            } else {
              Dafny.ISequence<Dafny.Rune> _3897_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3897_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3894_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3892_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1628;
              DCOMP._IOwnership _out1629;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3897_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1628, out _out1629);
              r = _out1628;
              resultingOwnership = _out1629;
            }
            readIdents = _3896_recIdents;
            return ;
          }
        } else if (_source159.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _3898___mcc_h192 = _source159.dtor_params;
          DAST._IType _3899___mcc_h193 = _source159.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _3900___mcc_h194 = _source159.dtor_body;
          bool _3901_isDatatype = _3580___mcc_h51;
          bool _3902_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3903_field = _3578___mcc_h49;
          DAST._IExpression _3904_on = _3577___mcc_h48;
          {
            RAST._IExpr _3905_onExpr;
            DCOMP._IOwnership _3906_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3907_recIdents;
            RAST._IExpr _out1630;
            DCOMP._IOwnership _out1631;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1632;
            (this).GenExpr(_3904_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1630, out _out1631, out _out1632);
            _3905_onExpr = _out1630;
            _3906_onOwned = _out1631;
            _3907_recIdents = _out1632;
            if ((_3901_isDatatype) || (_3902_isConstant)) {
              r = RAST.Expr.create_Call((_3905_onExpr).Sel(DCOMP.__default.escapeIdent(_3903_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1633;
              DCOMP._IOwnership _out1634;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1633, out _out1634);
              r = _out1633;
              resultingOwnership = _out1634;
            } else {
              Dafny.ISequence<Dafny.Rune> _3908_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3908_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3905_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3903_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1635;
              DCOMP._IOwnership _out1636;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3908_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1635, out _out1636);
              r = _out1635;
              resultingOwnership = _out1636;
            }
            readIdents = _3907_recIdents;
            return ;
          }
        } else if (_source159.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _3909___mcc_h198 = _source159.dtor_values;
          DAST._IType _3910___mcc_h199 = _source159.dtor_retType;
          DAST._IExpression _3911___mcc_h200 = _source159.dtor_expr;
          bool _3912_isDatatype = _3580___mcc_h51;
          bool _3913_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3914_field = _3578___mcc_h49;
          DAST._IExpression _3915_on = _3577___mcc_h48;
          {
            RAST._IExpr _3916_onExpr;
            DCOMP._IOwnership _3917_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3918_recIdents;
            RAST._IExpr _out1637;
            DCOMP._IOwnership _out1638;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1639;
            (this).GenExpr(_3915_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1637, out _out1638, out _out1639);
            _3916_onExpr = _out1637;
            _3917_onOwned = _out1638;
            _3918_recIdents = _out1639;
            if ((_3912_isDatatype) || (_3913_isConstant)) {
              r = RAST.Expr.create_Call((_3916_onExpr).Sel(DCOMP.__default.escapeIdent(_3914_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1640;
              DCOMP._IOwnership _out1641;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1640, out _out1641);
              r = _out1640;
              resultingOwnership = _out1641;
            } else {
              Dafny.ISequence<Dafny.Rune> _3919_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3919_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3916_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3914_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1642;
              DCOMP._IOwnership _out1643;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3919_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1642, out _out1643);
              r = _out1642;
              resultingOwnership = _out1643;
            }
            readIdents = _3918_recIdents;
            return ;
          }
        } else if (_source159.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _3920___mcc_h204 = _source159.dtor_name;
          DAST._IType _3921___mcc_h205 = _source159.dtor_typ;
          DAST._IExpression _3922___mcc_h206 = _source159.dtor_value;
          DAST._IExpression _3923___mcc_h207 = _source159.dtor_iifeBody;
          bool _3924_isDatatype = _3580___mcc_h51;
          bool _3925_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3926_field = _3578___mcc_h49;
          DAST._IExpression _3927_on = _3577___mcc_h48;
          {
            RAST._IExpr _3928_onExpr;
            DCOMP._IOwnership _3929_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3930_recIdents;
            RAST._IExpr _out1644;
            DCOMP._IOwnership _out1645;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1646;
            (this).GenExpr(_3927_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1644, out _out1645, out _out1646);
            _3928_onExpr = _out1644;
            _3929_onOwned = _out1645;
            _3930_recIdents = _out1646;
            if ((_3924_isDatatype) || (_3925_isConstant)) {
              r = RAST.Expr.create_Call((_3928_onExpr).Sel(DCOMP.__default.escapeIdent(_3926_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1647;
              DCOMP._IOwnership _out1648;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1647, out _out1648);
              r = _out1647;
              resultingOwnership = _out1648;
            } else {
              Dafny.ISequence<Dafny.Rune> _3931_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3931_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3928_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3926_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1649;
              DCOMP._IOwnership _out1650;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3931_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1649, out _out1650);
              r = _out1649;
              resultingOwnership = _out1650;
            }
            readIdents = _3930_recIdents;
            return ;
          }
        } else if (_source159.is_Apply) {
          DAST._IExpression _3932___mcc_h212 = _source159.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _3933___mcc_h213 = _source159.dtor_args;
          bool _3934_isDatatype = _3580___mcc_h51;
          bool _3935_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3936_field = _3578___mcc_h49;
          DAST._IExpression _3937_on = _3577___mcc_h48;
          {
            RAST._IExpr _3938_onExpr;
            DCOMP._IOwnership _3939_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3940_recIdents;
            RAST._IExpr _out1651;
            DCOMP._IOwnership _out1652;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1653;
            (this).GenExpr(_3937_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1651, out _out1652, out _out1653);
            _3938_onExpr = _out1651;
            _3939_onOwned = _out1652;
            _3940_recIdents = _out1653;
            if ((_3934_isDatatype) || (_3935_isConstant)) {
              r = RAST.Expr.create_Call((_3938_onExpr).Sel(DCOMP.__default.escapeIdent(_3936_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1654;
              DCOMP._IOwnership _out1655;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1654, out _out1655);
              r = _out1654;
              resultingOwnership = _out1655;
            } else {
              Dafny.ISequence<Dafny.Rune> _3941_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3941_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3938_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3936_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1656;
              DCOMP._IOwnership _out1657;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3941_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1656, out _out1657);
              r = _out1656;
              resultingOwnership = _out1657;
            }
            readIdents = _3940_recIdents;
            return ;
          }
        } else if (_source159.is_TypeTest) {
          DAST._IExpression _3942___mcc_h216 = _source159.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3943___mcc_h217 = _source159.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _3944___mcc_h218 = _source159.dtor_variant;
          bool _3945_isDatatype = _3580___mcc_h51;
          bool _3946_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3947_field = _3578___mcc_h49;
          DAST._IExpression _3948_on = _3577___mcc_h48;
          {
            RAST._IExpr _3949_onExpr;
            DCOMP._IOwnership _3950_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3951_recIdents;
            RAST._IExpr _out1658;
            DCOMP._IOwnership _out1659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1660;
            (this).GenExpr(_3948_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1658, out _out1659, out _out1660);
            _3949_onExpr = _out1658;
            _3950_onOwned = _out1659;
            _3951_recIdents = _out1660;
            if ((_3945_isDatatype) || (_3946_isConstant)) {
              r = RAST.Expr.create_Call((_3949_onExpr).Sel(DCOMP.__default.escapeIdent(_3947_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1661;
              DCOMP._IOwnership _out1662;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1661, out _out1662);
              r = _out1661;
              resultingOwnership = _out1662;
            } else {
              Dafny.ISequence<Dafny.Rune> _3952_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3952_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3949_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3947_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1663;
              DCOMP._IOwnership _out1664;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3952_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1663, out _out1664);
              r = _out1663;
              resultingOwnership = _out1664;
            }
            readIdents = _3951_recIdents;
            return ;
          }
        } else if (_source159.is_InitializationValue) {
          DAST._IType _3953___mcc_h222 = _source159.dtor_typ;
          bool _3954_isDatatype = _3580___mcc_h51;
          bool _3955_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3956_field = _3578___mcc_h49;
          DAST._IExpression _3957_on = _3577___mcc_h48;
          {
            RAST._IExpr _3958_onExpr;
            DCOMP._IOwnership _3959_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3960_recIdents;
            RAST._IExpr _out1665;
            DCOMP._IOwnership _out1666;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1667;
            (this).GenExpr(_3957_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1665, out _out1666, out _out1667);
            _3958_onExpr = _out1665;
            _3959_onOwned = _out1666;
            _3960_recIdents = _out1667;
            if ((_3954_isDatatype) || (_3955_isConstant)) {
              r = RAST.Expr.create_Call((_3958_onExpr).Sel(DCOMP.__default.escapeIdent(_3956_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1668;
              DCOMP._IOwnership _out1669;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1668, out _out1669);
              r = _out1668;
              resultingOwnership = _out1669;
            } else {
              Dafny.ISequence<Dafny.Rune> _3961_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3961_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3958_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3956_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1670;
              DCOMP._IOwnership _out1671;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3961_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1670, out _out1671);
              r = _out1670;
              resultingOwnership = _out1671;
            }
            readIdents = _3960_recIdents;
            return ;
          }
        } else if (_source159.is_BoolBoundedPool) {
          bool _3962_isDatatype = _3580___mcc_h51;
          bool _3963_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3964_field = _3578___mcc_h49;
          DAST._IExpression _3965_on = _3577___mcc_h48;
          {
            RAST._IExpr _3966_onExpr;
            DCOMP._IOwnership _3967_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3968_recIdents;
            RAST._IExpr _out1672;
            DCOMP._IOwnership _out1673;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1674;
            (this).GenExpr(_3965_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1672, out _out1673, out _out1674);
            _3966_onExpr = _out1672;
            _3967_onOwned = _out1673;
            _3968_recIdents = _out1674;
            if ((_3962_isDatatype) || (_3963_isConstant)) {
              r = RAST.Expr.create_Call((_3966_onExpr).Sel(DCOMP.__default.escapeIdent(_3964_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1675;
              DCOMP._IOwnership _out1676;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1675, out _out1676);
              r = _out1675;
              resultingOwnership = _out1676;
            } else {
              Dafny.ISequence<Dafny.Rune> _3969_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3969_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3966_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3964_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1677;
              DCOMP._IOwnership _out1678;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3969_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1677, out _out1678);
              r = _out1677;
              resultingOwnership = _out1678;
            }
            readIdents = _3968_recIdents;
            return ;
          }
        } else if (_source159.is_SetBoundedPool) {
          DAST._IExpression _3970___mcc_h224 = _source159.dtor_of;
          bool _3971_isDatatype = _3580___mcc_h51;
          bool _3972_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3973_field = _3578___mcc_h49;
          DAST._IExpression _3974_on = _3577___mcc_h48;
          {
            RAST._IExpr _3975_onExpr;
            DCOMP._IOwnership _3976_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3977_recIdents;
            RAST._IExpr _out1679;
            DCOMP._IOwnership _out1680;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1681;
            (this).GenExpr(_3974_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1679, out _out1680, out _out1681);
            _3975_onExpr = _out1679;
            _3976_onOwned = _out1680;
            _3977_recIdents = _out1681;
            if ((_3971_isDatatype) || (_3972_isConstant)) {
              r = RAST.Expr.create_Call((_3975_onExpr).Sel(DCOMP.__default.escapeIdent(_3973_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1682;
              DCOMP._IOwnership _out1683;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1682, out _out1683);
              r = _out1682;
              resultingOwnership = _out1683;
            } else {
              Dafny.ISequence<Dafny.Rune> _3978_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3978_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3975_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3973_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1684;
              DCOMP._IOwnership _out1685;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3978_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1684, out _out1685);
              r = _out1684;
              resultingOwnership = _out1685;
            }
            readIdents = _3977_recIdents;
            return ;
          }
        } else if (_source159.is_SeqBoundedPool) {
          DAST._IExpression _3979___mcc_h226 = _source159.dtor_of;
          bool _3980___mcc_h227 = _source159.dtor_includeDuplicates;
          bool _3981_isDatatype = _3580___mcc_h51;
          bool _3982_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3983_field = _3578___mcc_h49;
          DAST._IExpression _3984_on = _3577___mcc_h48;
          {
            RAST._IExpr _3985_onExpr;
            DCOMP._IOwnership _3986_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3987_recIdents;
            RAST._IExpr _out1686;
            DCOMP._IOwnership _out1687;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1688;
            (this).GenExpr(_3984_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1686, out _out1687, out _out1688);
            _3985_onExpr = _out1686;
            _3986_onOwned = _out1687;
            _3987_recIdents = _out1688;
            if ((_3981_isDatatype) || (_3982_isConstant)) {
              r = RAST.Expr.create_Call((_3985_onExpr).Sel(DCOMP.__default.escapeIdent(_3983_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1689;
              DCOMP._IOwnership _out1690;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1689, out _out1690);
              r = _out1689;
              resultingOwnership = _out1690;
            } else {
              Dafny.ISequence<Dafny.Rune> _3988_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3988_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3985_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3983_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1691;
              DCOMP._IOwnership _out1692;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3988_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1691, out _out1692);
              r = _out1691;
              resultingOwnership = _out1692;
            }
            readIdents = _3987_recIdents;
            return ;
          }
        } else {
          DAST._IExpression _3989___mcc_h230 = _source159.dtor_lo;
          DAST._IExpression _3990___mcc_h231 = _source159.dtor_hi;
          bool _3991_isDatatype = _3580___mcc_h51;
          bool _3992_isConstant = _3579___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3993_field = _3578___mcc_h49;
          DAST._IExpression _3994_on = _3577___mcc_h48;
          {
            RAST._IExpr _3995_onExpr;
            DCOMP._IOwnership _3996_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3997_recIdents;
            RAST._IExpr _out1693;
            DCOMP._IOwnership _out1694;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1695;
            (this).GenExpr(_3994_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1693, out _out1694, out _out1695);
            _3995_onExpr = _out1693;
            _3996_onOwned = _out1694;
            _3997_recIdents = _out1695;
            if ((_3991_isDatatype) || (_3992_isConstant)) {
              r = RAST.Expr.create_Call((_3995_onExpr).Sel(DCOMP.__default.escapeIdent(_3993_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1696;
              DCOMP._IOwnership _out1697;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1696, out _out1697);
              r = _out1696;
              resultingOwnership = _out1697;
            } else {
              Dafny.ISequence<Dafny.Rune> _3998_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3998_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3995_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3993_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1698;
              DCOMP._IOwnership _out1699;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3998_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1698, out _out1699);
              r = _out1698;
              resultingOwnership = _out1699;
            }
            readIdents = _3997_recIdents;
            return ;
          }
        }
      } else if (_source156.is_SelectFn) {
        DAST._IExpression _3999___mcc_h234 = _source156.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _4000___mcc_h235 = _source156.dtor_field;
        bool _4001___mcc_h236 = _source156.dtor_onDatatype;
        bool _4002___mcc_h237 = _source156.dtor_isStatic;
        BigInteger _4003___mcc_h238 = _source156.dtor_arity;
        BigInteger _4004_arity = _4003___mcc_h238;
        bool _4005_isStatic = _4002___mcc_h237;
        bool _4006_isDatatype = _4001___mcc_h236;
        Dafny.ISequence<Dafny.Rune> _4007_field = _4000___mcc_h235;
        DAST._IExpression _4008_on = _3999___mcc_h234;
        {
          RAST._IExpr _4009_onExpr;
          DCOMP._IOwnership _4010_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4011_recIdents;
          RAST._IExpr _out1700;
          DCOMP._IOwnership _out1701;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1702;
          (this).GenExpr(_4008_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1700, out _out1701, out _out1702);
          _4009_onExpr = _out1700;
          _4010_onOwned = _out1701;
          _4011_recIdents = _out1702;
          Dafny.ISequence<Dafny.Rune> _4012_s = Dafny.Sequence<Dafny.Rune>.Empty;
          Dafny.ISequence<Dafny.Rune> _4013_onString;
          _4013_onString = (_4009_onExpr)._ToString(DCOMP.__default.IND);
          if (_4005_isStatic) {
            _4012_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4013_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_4007_field));
          } else {
            _4012_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            _4012_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4012_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _4013_onString), ((object.Equals(_4010_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _4014_args;
            _4014_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _4015_i;
            _4015_i = BigInteger.Zero;
            while ((_4015_i) < (_4004_arity)) {
              if ((_4015_i).Sign == 1) {
                _4014_args = Dafny.Sequence<Dafny.Rune>.Concat(_4014_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _4014_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4014_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_4015_i));
              _4015_i = (_4015_i) + (BigInteger.One);
            }
            _4012_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4012_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _4014_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            _4012_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4012_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _4007_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _4014_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            _4012_s = Dafny.Sequence<Dafny.Rune>.Concat(_4012_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _4012_s = Dafny.Sequence<Dafny.Rune>.Concat(_4012_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          Dafny.ISequence<Dafny.Rune> _4016_typeShape;
          _4016_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
          BigInteger _4017_i;
          _4017_i = BigInteger.Zero;
          while ((_4017_i) < (_4004_arity)) {
            if ((_4017_i).Sign == 1) {
              _4016_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4016_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            _4016_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4016_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
            _4017_i = (_4017_i) + (BigInteger.One);
          }
          _4016_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4016_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
          _4012_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper(::std::rc::Rc::new("), _4012_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _4016_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">)"));
          r = RAST.Expr.create_RawExpr(_4012_s);
          RAST._IExpr _out1703;
          DCOMP._IOwnership _out1704;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1703, out _out1704);
          r = _out1703;
          resultingOwnership = _out1704;
          readIdents = _4011_recIdents;
          return ;
        }
      } else if (_source156.is_Index) {
        DAST._IExpression _4018___mcc_h239 = _source156.dtor_expr;
        DAST._ICollKind _4019___mcc_h240 = _source156.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _4020___mcc_h241 = _source156.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _4021_indices = _4020___mcc_h241;
        DAST._ICollKind _4022_collKind = _4019___mcc_h240;
        DAST._IExpression _4023_on = _4018___mcc_h239;
        {
          RAST._IExpr _4024_onExpr;
          DCOMP._IOwnership _4025_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4026_recIdents;
          RAST._IExpr _out1705;
          DCOMP._IOwnership _out1706;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1707;
          (this).GenExpr(_4023_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1705, out _out1706, out _out1707);
          _4024_onExpr = _out1705;
          _4025_onOwned = _out1706;
          _4026_recIdents = _out1707;
          readIdents = _4026_recIdents;
          r = _4024_onExpr;
          BigInteger _4027_i;
          _4027_i = BigInteger.Zero;
          while ((_4027_i) < (new BigInteger((_4021_indices).Count))) {
            if (object.Equals(_4022_collKind, DAST.CollKind.create_Array())) {
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IExpr _4028_idx;
            DCOMP._IOwnership _4029_idxOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4030_recIdentsIdx;
            RAST._IExpr _out1708;
            DCOMP._IOwnership _out1709;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1710;
            (this).GenExpr((_4021_indices).Select(_4027_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1708, out _out1709, out _out1710);
            _4028_idx = _out1708;
            _4029_idxOwned = _out1709;
            _4030_recIdentsIdx = _out1710;
            r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_4028_idx);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4030_recIdentsIdx);
            _4027_i = (_4027_i) + (BigInteger.One);
          }
          RAST._IExpr _out1711;
          DCOMP._IOwnership _out1712;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1711, out _out1712);
          r = _out1711;
          resultingOwnership = _out1712;
          return ;
        }
      } else if (_source156.is_IndexRange) {
        DAST._IExpression _4031___mcc_h242 = _source156.dtor_expr;
        bool _4032___mcc_h243 = _source156.dtor_isArray;
        Std.Wrappers._IOption<DAST._IExpression> _4033___mcc_h244 = _source156.dtor_low;
        Std.Wrappers._IOption<DAST._IExpression> _4034___mcc_h245 = _source156.dtor_high;
        Std.Wrappers._IOption<DAST._IExpression> _4035_high = _4034___mcc_h245;
        Std.Wrappers._IOption<DAST._IExpression> _4036_low = _4033___mcc_h244;
        bool _4037_isArray = _4032___mcc_h243;
        DAST._IExpression _4038_on = _4031___mcc_h242;
        {
          RAST._IExpr _4039_onExpr;
          DCOMP._IOwnership _4040_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4041_recIdents;
          RAST._IExpr _out1713;
          DCOMP._IOwnership _out1714;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1715;
          (this).GenExpr(_4038_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1713, out _out1714, out _out1715);
          _4039_onExpr = _out1713;
          _4040_onOwned = _out1714;
          _4041_recIdents = _out1715;
          readIdents = _4041_recIdents;
          Dafny.ISequence<Dafny.Rune> _4042_methodName;
          _4042_methodName = (((_4036_low).is_Some) ? ((((_4035_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_4035_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
          Dafny.ISequence<RAST._IExpr> _4043_arguments;
          _4043_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          Std.Wrappers._IOption<DAST._IExpression> _source160 = _4036_low;
          if (_source160.is_None) {
          } else {
            DAST._IExpression _4044___mcc_h274 = _source160.dtor_value;
            DAST._IExpression _4045_l = _4044___mcc_h274;
            {
              RAST._IExpr _4046_lExpr;
              DCOMP._IOwnership _4047___v118;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4048_recIdentsL;
              RAST._IExpr _out1716;
              DCOMP._IOwnership _out1717;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1718;
              (this).GenExpr(_4045_l, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1716, out _out1717, out _out1718);
              _4046_lExpr = _out1716;
              _4047___v118 = _out1717;
              _4048_recIdentsL = _out1718;
              _4043_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4043_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4046_lExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4048_recIdentsL);
            }
          }
          Std.Wrappers._IOption<DAST._IExpression> _source161 = _4035_high;
          if (_source161.is_None) {
          } else {
            DAST._IExpression _4049___mcc_h275 = _source161.dtor_value;
            DAST._IExpression _4050_h = _4049___mcc_h275;
            {
              RAST._IExpr _4051_hExpr;
              DCOMP._IOwnership _4052___v119;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4053_recIdentsH;
              RAST._IExpr _out1719;
              DCOMP._IOwnership _out1720;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1721;
              (this).GenExpr(_4050_h, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1719, out _out1720, out _out1721);
              _4051_hExpr = _out1719;
              _4052___v119 = _out1720;
              _4053_recIdentsH = _out1721;
              _4043_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4043_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4051_hExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4053_recIdentsH);
            }
          }
          r = _4039_onExpr;
          if (_4037_isArray) {
            if (!(_4042_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              _4042_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _4042_methodName);
            }
            r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _4042_methodName))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _4043_arguments);
          } else {
            if (!(_4042_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              r = ((r).Sel(_4042_methodName)).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _4043_arguments);
            }
          }
          RAST._IExpr _out1722;
          DCOMP._IOwnership _out1723;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1722, out _out1723);
          r = _out1722;
          resultingOwnership = _out1723;
          return ;
        }
      } else if (_source156.is_TupleSelect) {
        DAST._IExpression _4054___mcc_h246 = _source156.dtor_expr;
        BigInteger _4055___mcc_h247 = _source156.dtor_index;
        BigInteger _4056_idx = _4055___mcc_h247;
        DAST._IExpression _4057_on = _4054___mcc_h246;
        {
          RAST._IExpr _4058_onExpr;
          DCOMP._IOwnership _4059_onOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4060_recIdents;
          RAST._IExpr _out1724;
          DCOMP._IOwnership _out1725;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1726;
          (this).GenExpr(_4057_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1724, out _out1725, out _out1726);
          _4058_onExpr = _out1724;
          _4059_onOwnership = _out1725;
          _4060_recIdents = _out1726;
          r = (_4058_onExpr).Sel(Std.Strings.__default.OfNat(_4056_idx));
          RAST._IExpr _out1727;
          DCOMP._IOwnership _out1728;
          DCOMP.COMP.FromOwnership(r, _4059_onOwnership, expectedOwnership, out _out1727, out _out1728);
          r = _out1727;
          resultingOwnership = _out1728;
          readIdents = _4060_recIdents;
          return ;
        }
      } else if (_source156.is_Call) {
        DAST._IExpression _4061___mcc_h248 = _source156.dtor_on;
        DAST._ICallName _4062___mcc_h249 = _source156.dtor_callName;
        Dafny.ISequence<DAST._IType> _4063___mcc_h250 = _source156.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _4064___mcc_h251 = _source156.dtor_args;
        Dafny.ISequence<DAST._IExpression> _4065_args = _4064___mcc_h251;
        Dafny.ISequence<DAST._IType> _4066_typeArgs = _4063___mcc_h250;
        DAST._ICallName _4067_name = _4062___mcc_h249;
        DAST._IExpression _4068_on = _4061___mcc_h248;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IType> _4069_typeExprs;
          _4069_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_4066_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _4070_typeI;
            _4070_typeI = BigInteger.Zero;
            while ((_4070_typeI) < (new BigInteger((_4066_typeArgs).Count))) {
              RAST._IType _4071_typeExpr;
              RAST._IType _out1729;
              _out1729 = (this).GenType((_4066_typeArgs).Select(_4070_typeI), false, false);
              _4071_typeExpr = _out1729;
              _4069_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_4069_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_4071_typeExpr));
              _4070_typeI = (_4070_typeI) + (BigInteger.One);
            }
          }
          Dafny.ISequence<RAST._IExpr> _4072_argExprs;
          _4072_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _4073_i;
          _4073_i = BigInteger.Zero;
          while ((_4073_i) < (new BigInteger((_4065_args).Count))) {
            RAST._IExpr _4074_argExpr;
            DCOMP._IOwnership _4075_argOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4076_argIdents;
            RAST._IExpr _out1730;
            DCOMP._IOwnership _out1731;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1732;
            (this).GenExpr((_4065_args).Select(_4073_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1730, out _out1731, out _out1732);
            _4074_argExpr = _out1730;
            _4075_argOwnership = _out1731;
            _4076_argIdents = _out1732;
            _4072_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_4072_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_4074_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4076_argIdents);
            _4073_i = (_4073_i) + (BigInteger.One);
          }
          RAST._IExpr _4077_onExpr;
          DCOMP._IOwnership _4078___v120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4079_recIdents;
          RAST._IExpr _out1733;
          DCOMP._IOwnership _out1734;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1735;
          (this).GenExpr(_4068_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1733, out _out1734, out _out1735);
          _4077_onExpr = _out1733;
          _4078___v120 = _out1734;
          _4079_recIdents = _out1735;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4079_recIdents);
          Dafny.ISequence<Dafny.Rune> _4080_renderedName;
          _4080_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source162) => {
            if (_source162.is_Name) {
              Dafny.ISequence<Dafny.Rune> _4081___mcc_h276 = _source162.dtor_name;
              Dafny.ISequence<Dafny.Rune> _4082_ident = _4081___mcc_h276;
              return DCOMP.__default.escapeIdent(_4082_ident);
            } else if (_source162.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source162.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source162.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_4067_name);
          DAST._IExpression _source163 = _4068_on;
          if (_source163.is_Literal) {
            DAST._ILiteral _4083___mcc_h277 = _source163.dtor_Literal_a0;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _4084___mcc_h279 = _source163.dtor_Ident_a0;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4085___mcc_h281 = _source163.dtor_Companion_a0;
            {
              _4077_onExpr = (_4077_onExpr).MSel(_4080_renderedName);
            }
          } else if (_source163.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _4086___mcc_h283 = _source163.dtor_Tuple_a0;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4087___mcc_h285 = _source163.dtor_path;
            Dafny.ISequence<DAST._IType> _4088___mcc_h286 = _source163.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _4089___mcc_h287 = _source163.dtor_args;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _4090___mcc_h291 = _source163.dtor_dims;
            DAST._IType _4091___mcc_h292 = _source163.dtor_typ;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4092___mcc_h295 = _source163.dtor_path;
            Dafny.ISequence<DAST._IType> _4093___mcc_h296 = _source163.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _4094___mcc_h297 = _source163.dtor_variant;
            bool _4095___mcc_h298 = _source163.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _4096___mcc_h299 = _source163.dtor_contents;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_Convert) {
            DAST._IExpression _4097___mcc_h305 = _source163.dtor_value;
            DAST._IType _4098___mcc_h306 = _source163.dtor_from;
            DAST._IType _4099___mcc_h307 = _source163.dtor_typ;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_SeqConstruct) {
            DAST._IExpression _4100___mcc_h311 = _source163.dtor_length;
            DAST._IExpression _4101___mcc_h312 = _source163.dtor_elem;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _4102___mcc_h315 = _source163.dtor_elements;
            DAST._IType _4103___mcc_h316 = _source163.dtor_typ;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _4104___mcc_h319 = _source163.dtor_elements;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _4105___mcc_h321 = _source163.dtor_elements;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4106___mcc_h323 = _source163.dtor_mapElems;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_MapBuilder) {
            DAST._IType _4107___mcc_h325 = _source163.dtor_keyType;
            DAST._IType _4108___mcc_h326 = _source163.dtor_valueType;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_SeqUpdate) {
            DAST._IExpression _4109___mcc_h329 = _source163.dtor_expr;
            DAST._IExpression _4110___mcc_h330 = _source163.dtor_indexExpr;
            DAST._IExpression _4111___mcc_h331 = _source163.dtor_value;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_MapUpdate) {
            DAST._IExpression _4112___mcc_h335 = _source163.dtor_expr;
            DAST._IExpression _4113___mcc_h336 = _source163.dtor_indexExpr;
            DAST._IExpression _4114___mcc_h337 = _source163.dtor_value;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_SetBuilder) {
            DAST._IType _4115___mcc_h341 = _source163.dtor_elemType;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_ToMultiset) {
            DAST._IExpression _4116___mcc_h343 = _source163.dtor_ToMultiset_a0;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_This) {
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_Ite) {
            DAST._IExpression _4117___mcc_h345 = _source163.dtor_cond;
            DAST._IExpression _4118___mcc_h346 = _source163.dtor_thn;
            DAST._IExpression _4119___mcc_h347 = _source163.dtor_els;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_UnOp) {
            DAST._IUnaryOp _4120___mcc_h351 = _source163.dtor_unOp;
            DAST._IExpression _4121___mcc_h352 = _source163.dtor_expr;
            DAST.Format._IUnaryOpFormat _4122___mcc_h353 = _source163.dtor_format1;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_BinOp) {
            DAST._IBinOp _4123___mcc_h357 = _source163.dtor_op;
            DAST._IExpression _4124___mcc_h358 = _source163.dtor_left;
            DAST._IExpression _4125___mcc_h359 = _source163.dtor_right;
            DAST.Format._IBinaryOpFormat _4126___mcc_h360 = _source163.dtor_format2;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_ArrayLen) {
            DAST._IExpression _4127___mcc_h365 = _source163.dtor_expr;
            BigInteger _4128___mcc_h366 = _source163.dtor_dim;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_MapKeys) {
            DAST._IExpression _4129___mcc_h369 = _source163.dtor_expr;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_MapValues) {
            DAST._IExpression _4130___mcc_h371 = _source163.dtor_expr;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_Select) {
            DAST._IExpression _4131___mcc_h373 = _source163.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4132___mcc_h374 = _source163.dtor_field;
            bool _4133___mcc_h375 = _source163.dtor_isConstant;
            bool _4134___mcc_h376 = _source163.dtor_onDatatype;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_SelectFn) {
            DAST._IExpression _4135___mcc_h381 = _source163.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4136___mcc_h382 = _source163.dtor_field;
            bool _4137___mcc_h383 = _source163.dtor_onDatatype;
            bool _4138___mcc_h384 = _source163.dtor_isStatic;
            BigInteger _4139___mcc_h385 = _source163.dtor_arity;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_Index) {
            DAST._IExpression _4140___mcc_h391 = _source163.dtor_expr;
            DAST._ICollKind _4141___mcc_h392 = _source163.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _4142___mcc_h393 = _source163.dtor_indices;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_IndexRange) {
            DAST._IExpression _4143___mcc_h397 = _source163.dtor_expr;
            bool _4144___mcc_h398 = _source163.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _4145___mcc_h399 = _source163.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _4146___mcc_h400 = _source163.dtor_high;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_TupleSelect) {
            DAST._IExpression _4147___mcc_h405 = _source163.dtor_expr;
            BigInteger _4148___mcc_h406 = _source163.dtor_index;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_Call) {
            DAST._IExpression _4149___mcc_h409 = _source163.dtor_on;
            DAST._ICallName _4150___mcc_h410 = _source163.dtor_callName;
            Dafny.ISequence<DAST._IType> _4151___mcc_h411 = _source163.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _4152___mcc_h412 = _source163.dtor_args;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _4153___mcc_h417 = _source163.dtor_params;
            DAST._IType _4154___mcc_h418 = _source163.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _4155___mcc_h419 = _source163.dtor_body;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4156___mcc_h423 = _source163.dtor_values;
            DAST._IType _4157___mcc_h424 = _source163.dtor_retType;
            DAST._IExpression _4158___mcc_h425 = _source163.dtor_expr;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _4159___mcc_h429 = _source163.dtor_name;
            DAST._IType _4160___mcc_h430 = _source163.dtor_typ;
            DAST._IExpression _4161___mcc_h431 = _source163.dtor_value;
            DAST._IExpression _4162___mcc_h432 = _source163.dtor_iifeBody;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_Apply) {
            DAST._IExpression _4163___mcc_h437 = _source163.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _4164___mcc_h438 = _source163.dtor_args;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_TypeTest) {
            DAST._IExpression _4165___mcc_h441 = _source163.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4166___mcc_h442 = _source163.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _4167___mcc_h443 = _source163.dtor_variant;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_InitializationValue) {
            DAST._IType _4168___mcc_h447 = _source163.dtor_typ;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_BoolBoundedPool) {
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_SetBoundedPool) {
            DAST._IExpression _4169___mcc_h449 = _source163.dtor_of;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else if (_source163.is_SeqBoundedPool) {
            DAST._IExpression _4170___mcc_h451 = _source163.dtor_of;
            bool _4171___mcc_h452 = _source163.dtor_includeDuplicates;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          } else {
            DAST._IExpression _4172___mcc_h455 = _source163.dtor_lo;
            DAST._IExpression _4173___mcc_h456 = _source163.dtor_hi;
            {
              _4077_onExpr = (_4077_onExpr).Sel(_4080_renderedName);
            }
          }
          r = RAST.Expr.create_Call(_4077_onExpr, _4069_typeExprs, _4072_argExprs);
          RAST._IExpr _out1736;
          DCOMP._IOwnership _out1737;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1736, out _out1737);
          r = _out1736;
          resultingOwnership = _out1737;
          return ;
        }
      } else if (_source156.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _4174___mcc_h252 = _source156.dtor_params;
        DAST._IType _4175___mcc_h253 = _source156.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _4176___mcc_h254 = _source156.dtor_body;
        Dafny.ISequence<DAST._IStatement> _4177_body = _4176___mcc_h254;
        DAST._IType _4178_retType = _4175___mcc_h253;
        Dafny.ISequence<DAST._IFormal> _4179_params = _4174___mcc_h252;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4180_paramNames;
          _4180_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4181_i;
          _4181_i = BigInteger.Zero;
          while ((_4181_i) < (new BigInteger((_4179_params).Count))) {
            _4180_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_4180_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_4179_params).Select(_4181_i)).dtor_name));
            _4181_i = (_4181_i) + (BigInteger.One);
          }
          RAST._IExpr _4182_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4183_recIdents;
          RAST._IExpr _out1738;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1739;
          (this).GenStmts(_4177_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _4180_paramNames, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out1738, out _out1739);
          _4182_recursiveGen = _out1738;
          _4183_recIdents = _out1739;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _4184_allReadCloned;
          _4184_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_4183_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _4185_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_4183_recIdents).Elements) {
              _4185_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
              if ((_4183_recIdents).Contains(_4185_next)) {
                goto after__ASSIGN_SUCH_THAT_3;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 3280)");
          after__ASSIGN_SUCH_THAT_3: ;
            if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_4185_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
              if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                _4184_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(_4184_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let _this = self.clone();\n"));
              }
            } else if (!((_4180_paramNames).Contains(_4185_next))) {
              _4184_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4184_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent(_4185_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), DCOMP.__default.escapeIdent(_4185_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4185_next));
            }
            _4183_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4183_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4185_next));
          }
          Dafny.ISequence<Dafny.Rune> _4186_paramsString;
          _4186_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          Dafny.ISequence<Dafny.Rune> _4187_paramTypes;
          _4187_paramTypes = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _4181_i = BigInteger.Zero;
          while ((_4181_i) < (new BigInteger((_4179_params).Count))) {
            if ((_4181_i).Sign == 1) {
              _4186_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_4186_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              _4187_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_4187_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IType _4188_typStr;
            RAST._IType _out1740;
            _out1740 = (this).GenType(((_4179_params).Select(_4181_i)).dtor_typ, false, true);
            _4188_typStr = _out1740;
            _4186_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4186_paramsString, DCOMP.__default.escapeIdent(((_4179_params).Select(_4181_i)).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (RAST.Type.create_Borrowed(_4188_typStr))._ToString(DCOMP.__default.IND));
            _4187_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_4187_paramTypes, (RAST.Type.create_Borrowed(_4188_typStr))._ToString(DCOMP.__default.IND));
            _4181_i = (_4181_i) + (BigInteger.One);
          }
          RAST._IType _4189_retTypeGen;
          RAST._IType _out1741;
          _out1741 = (this).GenType(_4178_retType, false, true);
          _4189_retTypeGen = _out1741;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn("), _4187_paramTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), (_4189_retTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>({\n")), _4184_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(move |")), _4186_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), (_4189_retTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), (_4182_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})")));
          RAST._IExpr _out1742;
          DCOMP._IOwnership _out1743;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1742, out _out1743);
          r = _out1742;
          resultingOwnership = _out1743;
          return ;
        }
      } else if (_source156.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4190___mcc_h255 = _source156.dtor_values;
        DAST._IType _4191___mcc_h256 = _source156.dtor_retType;
        DAST._IExpression _4192___mcc_h257 = _source156.dtor_expr;
        DAST._IExpression _4193_expr = _4192___mcc_h257;
        DAST._IType _4194_retType = _4191___mcc_h256;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4195_values = _4190___mcc_h255;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4196_paramNames;
          _4196_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4197_paramNamesSet;
          _4197_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _4198_i;
          _4198_i = BigInteger.Zero;
          while ((_4198_i) < (new BigInteger((_4195_values).Count))) {
            _4196_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_4196_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((_4195_values).Select(_4198_i)).dtor__0).dtor_name));
            _4197_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4197_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((((_4195_values).Select(_4198_i)).dtor__0).dtor_name));
            _4198_i = (_4198_i) + (BigInteger.One);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _4199_s;
          _4199_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          Dafny.ISequence<Dafny.Rune> _4200_paramsString;
          _4200_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _4198_i = BigInteger.Zero;
          while ((_4198_i) < (new BigInteger((_4195_values).Count))) {
            if ((_4198_i).Sign == 1) {
              _4200_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_4200_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IType _4201_typStr;
            RAST._IType _out1744;
            _out1744 = (this).GenType((((_4195_values).Select(_4198_i)).dtor__0).dtor_typ, false, true);
            _4201_typStr = _out1744;
            RAST._IExpr _4202_valueGen;
            DCOMP._IOwnership _4203___v123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4204_recIdents;
            RAST._IExpr _out1745;
            DCOMP._IOwnership _out1746;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1747;
            (this).GenExpr(((_4195_values).Select(_4198_i)).dtor__1, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1745, out _out1746, out _out1747);
            _4202_valueGen = _out1745;
            _4203___v123 = _out1746;
            _4204_recIdents = _out1747;
            _4199_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4199_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent((((_4195_values).Select(_4198_i)).dtor__0).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_4201_typStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4204_recIdents);
            _4199_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4199_s, (_4202_valueGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            _4198_i = (_4198_i) + (BigInteger.One);
          }
          RAST._IExpr _4205_recGen;
          DCOMP._IOwnership _4206_recOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4207_recIdents;
          RAST._IExpr _out1748;
          DCOMP._IOwnership _out1749;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1750;
          (this).GenExpr(_4193_expr, selfIdent, _4196_paramNames, expectedOwnership, out _out1748, out _out1749, out _out1750);
          _4205_recGen = _out1748;
          _4206_recOwned = _out1749;
          _4207_recIdents = _out1750;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4207_recIdents, _4197_paramNamesSet);
          _4199_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4199_s, (_4205_recGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          r = RAST.Expr.create_RawExpr(_4199_s);
          RAST._IExpr _out1751;
          DCOMP._IOwnership _out1752;
          DCOMP.COMP.FromOwnership(r, _4206_recOwned, expectedOwnership, out _out1751, out _out1752);
          r = _out1751;
          resultingOwnership = _out1752;
          return ;
        }
      } else if (_source156.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _4208___mcc_h258 = _source156.dtor_name;
        DAST._IType _4209___mcc_h259 = _source156.dtor_typ;
        DAST._IExpression _4210___mcc_h260 = _source156.dtor_value;
        DAST._IExpression _4211___mcc_h261 = _source156.dtor_iifeBody;
        DAST._IExpression _4212_iifeBody = _4211___mcc_h261;
        DAST._IExpression _4213_value = _4210___mcc_h260;
        DAST._IType _4214_tpe = _4209___mcc_h259;
        Dafny.ISequence<Dafny.Rune> _4215_name = _4208___mcc_h258;
        {
          RAST._IExpr _4216_valueGen;
          DCOMP._IOwnership _4217___v124;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4218_recIdents;
          RAST._IExpr _out1753;
          DCOMP._IOwnership _out1754;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1755;
          (this).GenExpr(_4213_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1753, out _out1754, out _out1755);
          _4216_valueGen = _out1753;
          _4217___v124 = _out1754;
          _4218_recIdents = _out1755;
          readIdents = _4218_recIdents;
          RAST._IType _4219_valueTypeGen;
          RAST._IType _out1756;
          _out1756 = (this).GenType(_4214_tpe, false, true);
          _4219_valueTypeGen = _out1756;
          RAST._IExpr _4220_bodyGen;
          DCOMP._IOwnership _4221___v125;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4222_bodyIdents;
          RAST._IExpr _out1757;
          DCOMP._IOwnership _out1758;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1759;
          (this).GenExpr(_4212_iifeBody, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1757, out _out1758, out _out1759);
          _4220_bodyGen = _out1757;
          _4221___v125 = _out1758;
          _4222_bodyIdents = _out1759;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4222_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_4215_name))));
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet "), DCOMP.__default.escapeIdent((_4215_name))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_4219_valueTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (_4216_valueGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), (_4220_bodyGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")));
          RAST._IExpr _out1760;
          DCOMP._IOwnership _out1761;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1760, out _out1761);
          r = _out1760;
          resultingOwnership = _out1761;
          return ;
        }
      } else if (_source156.is_Apply) {
        DAST._IExpression _4223___mcc_h262 = _source156.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _4224___mcc_h263 = _source156.dtor_args;
        Dafny.ISequence<DAST._IExpression> _4225_args = _4224___mcc_h263;
        DAST._IExpression _4226_func = _4223___mcc_h262;
        {
          RAST._IExpr _4227_funcExpr;
          DCOMP._IOwnership _4228___v126;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4229_recIdents;
          RAST._IExpr _out1762;
          DCOMP._IOwnership _out1763;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1764;
          (this).GenExpr(_4226_func, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1762, out _out1763, out _out1764);
          _4227_funcExpr = _out1762;
          _4228___v126 = _out1763;
          _4229_recIdents = _out1764;
          readIdents = _4229_recIdents;
          Dafny.ISequence<Dafny.Rune> _4230_argString;
          _4230_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _4231_i;
          _4231_i = BigInteger.Zero;
          while ((_4231_i) < (new BigInteger((_4225_args).Count))) {
            if ((_4231_i).Sign == 1) {
              _4230_argString = Dafny.Sequence<Dafny.Rune>.Concat(_4230_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IExpr _4232_argExpr;
            DCOMP._IOwnership _4233_argOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4234_argIdents;
            RAST._IExpr _out1765;
            DCOMP._IOwnership _out1766;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1767;
            (this).GenExpr((_4225_args).Select(_4231_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1765, out _out1766, out _out1767);
            _4232_argExpr = _out1765;
            _4233_argOwned = _out1766;
            _4234_argIdents = _out1767;
            Dafny.ISequence<Dafny.Rune> _4235_argExprString;
            _4235_argExprString = (_4232_argExpr)._ToString(DCOMP.__default.IND);
            if (object.Equals(_4233_argOwned, DCOMP.Ownership.create_OwnershipOwned())) {
              _4235_argExprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _4235_argExprString);
            }
            _4230_argString = Dafny.Sequence<Dafny.Rune>.Concat(_4230_argString, _4235_argExprString);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4234_argIdents);
            _4231_i = (_4231_i) + (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_4227_funcExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _4230_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))")));
          RAST._IExpr _out1768;
          DCOMP._IOwnership _out1769;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1768, out _out1769);
          r = _out1768;
          resultingOwnership = _out1769;
          return ;
        }
      } else if (_source156.is_TypeTest) {
        DAST._IExpression _4236___mcc_h264 = _source156.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4237___mcc_h265 = _source156.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _4238___mcc_h266 = _source156.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _4239_variant = _4238___mcc_h266;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4240_dType = _4237___mcc_h265;
        DAST._IExpression _4241_on = _4236___mcc_h264;
        {
          RAST._IExpr _4242_exprGen;
          DCOMP._IOwnership _4243___v127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4244_recIdents;
          RAST._IExpr _out1770;
          DCOMP._IOwnership _out1771;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1772;
          (this).GenExpr(_4241_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1770, out _out1771, out _out1772);
          _4242_exprGen = _out1770;
          _4243___v127 = _out1771;
          _4244_recIdents = _out1772;
          Dafny.ISequence<Dafny.Rune> _4245_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1773;
          _out1773 = DCOMP.COMP.GenPath(_4240_dType);
          _4245_dTypePath = _out1773;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), (_4242_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _4245_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_4239_variant)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })")));
          RAST._IExpr _out1774;
          DCOMP._IOwnership _out1775;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1774, out _out1775);
          r = _out1774;
          resultingOwnership = _out1775;
          readIdents = _4244_recIdents;
          return ;
        }
      } else if (_source156.is_InitializationValue) {
        DAST._IType _4246___mcc_h267 = _source156.dtor_typ;
        DAST._IType _4247_typ = _4246___mcc_h267;
        {
          RAST._IType _4248_typExpr;
          RAST._IType _out1776;
          _out1776 = (this).GenType(_4247_typ, false, false);
          _4248_typExpr = _out1776;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_4248_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
          RAST._IExpr _out1777;
          DCOMP._IOwnership _out1778;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1777, out _out1778);
          r = _out1777;
          resultingOwnership = _out1778;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source156.is_BoolBoundedPool) {
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
      } else if (_source156.is_SetBoundedPool) {
        DAST._IExpression _4249___mcc_h268 = _source156.dtor_of;
        DAST._IExpression _4250_of = _4249___mcc_h268;
        {
          RAST._IExpr _4251_exprGen;
          DCOMP._IOwnership _4252___v128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4253_recIdents;
          RAST._IExpr _out1781;
          DCOMP._IOwnership _out1782;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1783;
          (this).GenExpr(_4250_of, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1781, out _out1782, out _out1783);
          _4251_exprGen = _out1781;
          _4252___v128 = _out1782;
          _4253_recIdents = _out1783;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_4251_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").iter()")));
          RAST._IExpr _out1784;
          DCOMP._IOwnership _out1785;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1784, out _out1785);
          r = _out1784;
          resultingOwnership = _out1785;
          readIdents = _4253_recIdents;
          return ;
        }
      } else if (_source156.is_SeqBoundedPool) {
        DAST._IExpression _4254___mcc_h269 = _source156.dtor_of;
        bool _4255___mcc_h270 = _source156.dtor_includeDuplicates;
        bool _4256_includeDuplicates = _4255___mcc_h270;
        DAST._IExpression _4257_of = _4254___mcc_h269;
        {
          RAST._IExpr _4258_exprGen;
          DCOMP._IOwnership _4259___v129;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4260_recIdents;
          RAST._IExpr _out1786;
          DCOMP._IOwnership _out1787;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1788;
          (this).GenExpr(_4257_of, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1786, out _out1787, out _out1788);
          _4258_exprGen = _out1786;
          _4259___v129 = _out1787;
          _4260_recIdents = _out1788;
          Dafny.ISequence<Dafny.Rune> _4261_s;
          _4261_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_4258_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").iter()"));
          if (!(_4256_includeDuplicates)) {
            _4261_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::itertools::Itertools::unique("), _4261_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          r = RAST.Expr.create_RawExpr(_4261_s);
          RAST._IExpr _out1789;
          DCOMP._IOwnership _out1790;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1789, out _out1790);
          r = _out1789;
          resultingOwnership = _out1790;
          readIdents = _4260_recIdents;
          return ;
        }
      } else {
        DAST._IExpression _4262___mcc_h271 = _source156.dtor_lo;
        DAST._IExpression _4263___mcc_h272 = _source156.dtor_hi;
        DAST._IExpression _4264_hi = _4263___mcc_h272;
        DAST._IExpression _4265_lo = _4262___mcc_h271;
        {
          RAST._IExpr _4266_lo;
          DCOMP._IOwnership _4267___v130;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4268_recIdentsLo;
          RAST._IExpr _out1791;
          DCOMP._IOwnership _out1792;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1793;
          (this).GenExpr(_4265_lo, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1791, out _out1792, out _out1793);
          _4266_lo = _out1791;
          _4267___v130 = _out1792;
          _4268_recIdentsLo = _out1793;
          RAST._IExpr _4269_hi;
          DCOMP._IOwnership _4270___v131;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4271_recIdentsHi;
          RAST._IExpr _out1794;
          DCOMP._IOwnership _out1795;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1796;
          (this).GenExpr(_4264_hi, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1794, out _out1795, out _out1796);
          _4269_hi = _out1794;
          _4270___v131 = _out1795;
          _4271_recIdentsHi = _out1796;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::integer_range("), (_4266_lo)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), (_4269_hi)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          RAST._IExpr _out1797;
          DCOMP._IOwnership _out1798;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1797, out _out1798);
          r = _out1797;
          resultingOwnership = _out1798;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4268_recIdentsLo, _4271_recIdentsHi);
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
      BigInteger _4272_i;
      _4272_i = BigInteger.Zero;
      while ((_4272_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _4273_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _4274_m;
        RAST._IMod _out1799;
        _out1799 = (this).GenModule((p).Select(_4272_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _4274_m = _out1799;
        _4273_generated = (_4274_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_4272_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _4273_generated);
        _4272_i = (_4272_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _4275_i;
      _4275_i = BigInteger.Zero;
      while ((_4275_i) < (new BigInteger((fullName).Count))) {
        if ((_4275_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeIdent((fullName).Select(_4275_i)));
        _4275_i = (_4275_i) + (BigInteger.One);
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