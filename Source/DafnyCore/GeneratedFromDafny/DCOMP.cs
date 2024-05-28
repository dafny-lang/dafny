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
      Dafny.ISequence<Dafny.Rune> _1390___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1390___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1390___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1390___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _1390___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1390___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1391___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1391___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1391___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1391___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _1391___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1391___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1392_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1392_r);
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
      Dafny.ISequence<RAST._IModDecl> _1393_body;
      Dafny.ISequence<RAST._IModDecl> _out15;
      _out15 = (this).GenModuleBody((mod).dtor_body, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
      _1393_body = _out15;
      s = (((mod).dtor_isExtern) ? (RAST.Mod.create_ExternMod(DCOMP.__default.escapeIdent((mod).dtor_name))) : (RAST.Mod.create_Mod(DCOMP.__default.escapeIdent((mod).dtor_name), _1393_body)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _1394_i;
      _1394_i = BigInteger.Zero;
      while ((_1394_i) < (new BigInteger((body).Count))) {
        Dafny.ISequence<RAST._IModDecl> _1395_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source44 = (body).Select(_1394_i);
        if (_source44.is_Module) {
          DAST._IModule _1396___mcc_h0 = _source44.dtor_Module_a0;
          DAST._IModule _1397_m = _1396___mcc_h0;
          RAST._IMod _1398_mm;
          RAST._IMod _out16;
          _out16 = (this).GenModule(_1397_m, containingPath);
          _1398_mm = _out16;
          _1395_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1398_mm));
        } else if (_source44.is_Class) {
          DAST._IClass _1399___mcc_h1 = _source44.dtor_Class_a0;
          DAST._IClass _1400_c = _1399___mcc_h1;
          Dafny.ISequence<RAST._IModDecl> _out17;
          _out17 = (this).GenClass(_1400_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1400_c).dtor_name)));
          _1395_generated = _out17;
        } else if (_source44.is_Trait) {
          DAST._ITrait _1401___mcc_h2 = _source44.dtor_Trait_a0;
          DAST._ITrait _1402_t = _1401___mcc_h2;
          Dafny.ISequence<Dafny.Rune> _1403_tt;
          Dafny.ISequence<Dafny.Rune> _out18;
          _out18 = (this).GenTrait(_1402_t, containingPath);
          _1403_tt = _out18;
          _1395_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_1403_tt));
        } else if (_source44.is_Newtype) {
          DAST._INewtype _1404___mcc_h3 = _source44.dtor_Newtype_a0;
          DAST._INewtype _1405_n = _1404___mcc_h3;
          Dafny.ISequence<RAST._IModDecl> _out19;
          _out19 = (this).GenNewtype(_1405_n);
          _1395_generated = _out19;
        } else {
          DAST._IDatatype _1406___mcc_h4 = _source44.dtor_Datatype_a0;
          DAST._IDatatype _1407_d = _1406___mcc_h4;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenDatatype(_1407_d);
          _1395_generated = _out20;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1395_generated);
        _1394_i = (_1394_i) + (BigInteger.One);
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
      BigInteger _1408_tpI;
      _1408_tpI = BigInteger.Zero;
      if ((new BigInteger((@params).Count)).Sign == 1) {
        while ((_1408_tpI) < (new BigInteger((@params).Count))) {
          DAST._IType _1409_tp;
          _1409_tp = (@params).Select(_1408_tpI);
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1409_tp));
          RAST._IType _1410_genTp;
          RAST._IType _out21;
          _out21 = (this).GenType(_1409_tp, false, false);
          _1410_genTp = _out21;
          typeParams = Dafny.Sequence<RAST._ITypeParam>.Concat(typeParams, Dafny.Sequence<RAST._ITypeParam>.FromElements(RAST.TypeParam.create((_1410_genTp)._ToString(DCOMP.__default.IND), Dafny.Sequence<RAST._IType>.FromElements())));
          _1408_tpI = (_1408_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<RAST._IType> _1411_baseConstraints;
      _1411_baseConstraints = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.CloneTrait, RAST.__default.DafnyPrintTrait, RAST.__default.StaticTrait);
      constrainedTypeParams = RAST.TypeParam.AddConstraintsMultiple(typeParams, _1411_baseConstraints);
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1412_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1413_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1414_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1415_whereConstraints;
      Dafny.ISet<DAST._IType> _out22;
      Dafny.ISequence<RAST._ITypeParam> _out23;
      Dafny.ISequence<RAST._ITypeParam> _out24;
      Dafny.ISequence<Dafny.Rune> _out25;
      (this).GenTypeParameters((c).dtor_typeParams, out _out22, out _out23, out _out24, out _out25);
      _1412_typeParamsSet = _out22;
      _1413_sTypeParams = _out23;
      _1414_sConstrainedTypeParams = _out24;
      _1415_whereConstraints = _out25;
      Dafny.ISequence<Dafny.Rune> _1416_constrainedTypeParams;
      _1416_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1414_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IFormal> _1417_fields;
      _1417_fields = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1418_fieldInits;
      _1418_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _1419_fieldI;
      _1419_fieldI = BigInteger.Zero;
      while ((_1419_fieldI) < (new BigInteger(((c).dtor_fields).Count))) {
        DAST._IField _1420_field;
        _1420_field = ((c).dtor_fields).Select(_1419_fieldI);
        RAST._IType _1421_fieldType;
        RAST._IType _out26;
        _out26 = (this).GenType(((_1420_field).dtor_formal).dtor_typ, false, false);
        _1421_fieldType = _out26;
        _1417_fields = Dafny.Sequence<RAST._IFormal>.Concat(_1417_fields, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub "), DCOMP.__default.escapeIdent(((_1420_field).dtor_formal).dtor_name)), RAST.Type.create_TypeApp(RAST.__default.refcell__type, Dafny.Sequence<RAST._IType>.FromElements(_1421_fieldType)))));
        Std.Wrappers._IOption<DAST._IExpression> _source45 = (_1420_field).dtor_defaultValue;
        if (_source45.is_None) {
          {
            _1418_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1418_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(((_1420_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new(::std::default::Default::default())")))));
          }
        } else {
          DAST._IExpression _1422___mcc_h0 = _source45.dtor_value;
          DAST._IExpression _1423_e = _1422___mcc_h0;
          {
            RAST._IExpr _1424_eStr;
            DCOMP._IOwnership _1425___v27;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1426___v28;
            RAST._IExpr _out27;
            DCOMP._IOwnership _out28;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out29;
            (this).GenExpr(_1423_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out27, out _out28, out _out29);
            _1424_eStr = _out27;
            _1425___v27 = _out28;
            _1426___v28 = _out29;
            _1418_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1418_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(((_1420_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1424_eStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
          }
        }
        _1419_fieldI = (_1419_fieldI) + (BigInteger.One);
      }
      BigInteger _1427_typeParamI;
      _1427_typeParamI = BigInteger.Zero;
      while ((_1427_typeParamI) < (new BigInteger(((c).dtor_typeParams).Count))) {
        RAST._IType _1428_tpeGen;
        RAST._IType _out30;
        _out30 = (this).GenType(((c).dtor_typeParams).Select(_1427_typeParamI), false, false);
        _1428_tpeGen = _out30;
        _1417_fields = Dafny.Sequence<RAST._IFormal>.Concat(_1417_fields, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1427_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1428_tpeGen)))));
        _1418_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1418_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1427_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
        _1427_typeParamI = (_1427_typeParamI) + (BigInteger.One);
      }
      RAST._IStruct _1429_struct;
      _1429_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.__default.escapeIdent((c).dtor_name), _1413_sTypeParams, RAST.Formals.create_NamedFormals(_1417_fields));
      Dafny.ISequence<RAST._IType> _1430_typeParamsAsTypes;
      _1430_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1431_typeParam) => {
        return RAST.__default.RawType((_1431_typeParam).dtor_content);
      })), _1413_sTypeParams);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1429_struct));
      Dafny.ISequence<RAST._IImplMember> _1432_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1433_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out31;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out32;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(path)), _1412_typeParamsSet, out _out31, out _out32);
      _1432_implBodyRaw = _out31;
      _1433_traitBodies = _out32;
      Dafny.ISequence<RAST._IImplMember> _1434_implBody;
      _1434_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(DCOMP.__default.escapeIdent((c).dtor_name), _1418_fieldInits))))), _1432_implBodyRaw);
      RAST._IImpl _1435_i;
      _1435_i = RAST.Impl.create_Impl(_1414_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1430_typeParamsAsTypes), _1415_whereConstraints, _1434_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1435_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1436_i;
        _1436_i = BigInteger.Zero;
        while ((_1436_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1437_superClass;
          _1437_superClass = ((c).dtor_superClasses).Select(_1436_i);
          DAST._IType _source46 = _1437_superClass;
          if (_source46.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1438___mcc_h1 = _source46.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1439___mcc_h2 = _source46.dtor_typeArgs;
            DAST._IResolvedType _1440___mcc_h3 = _source46.dtor_resolved;
            DAST._IResolvedType _source47 = _1440___mcc_h3;
            if (_source47.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1441___mcc_h7 = _source47.dtor_path;
            } else if (_source47.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1442___mcc_h9 = _source47.dtor_path;
              Dafny.ISequence<DAST._IType> _1443_typeArgs = _1439___mcc_h2;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1444_traitPath = _1438___mcc_h1;
              {
                Dafny.ISequence<Dafny.Rune> _1445_pathStr;
                Dafny.ISequence<Dafny.Rune> _out33;
                _out33 = DCOMP.COMP.GenPath(_1444_traitPath);
                _1445_pathStr = _out33;
                Dafny.ISequence<RAST._IType> _1446_typeArgs;
                Dafny.ISequence<RAST._IType> _out34;
                _out34 = (this).GenTypeArgs(_1443_typeArgs, false, false);
                _1446_typeArgs = _out34;
                Dafny.ISequence<RAST._IImplMember> _1447_body;
                _1447_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1433_traitBodies).Contains(_1444_traitPath)) {
                  _1447_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1433_traitBodies,_1444_traitPath);
                }
                Dafny.ISequence<Dafny.Rune> _1448_genSelfPath;
                Dafny.ISequence<Dafny.Rune> _out35;
                _out35 = DCOMP.COMP.GenPath(path);
                _1448_genSelfPath = _out35;
                RAST._IModDecl _1449_x;
                _1449_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1414_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_pathStr), _1446_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_genSelfPath), _1430_typeParamsAsTypes)), _1415_whereConstraints, _1447_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1449_x));
              }
            } else {
              DAST._IType _1450___mcc_h11 = _source47.dtor_baseType;
              DAST._INewtypeRange _1451___mcc_h12 = _source47.dtor_range;
              bool _1452___mcc_h13 = _source47.dtor_erase;
            }
          } else if (_source46.is_Nullable) {
            DAST._IType _1453___mcc_h17 = _source46.dtor_Nullable_a0;
          } else if (_source46.is_Tuple) {
            Dafny.ISequence<DAST._IType> _1454___mcc_h19 = _source46.dtor_Tuple_a0;
          } else if (_source46.is_Array) {
            DAST._IType _1455___mcc_h21 = _source46.dtor_element;
            BigInteger _1456___mcc_h22 = _source46.dtor_dims;
          } else if (_source46.is_Seq) {
            DAST._IType _1457___mcc_h25 = _source46.dtor_element;
          } else if (_source46.is_Set) {
            DAST._IType _1458___mcc_h27 = _source46.dtor_element;
          } else if (_source46.is_Multiset) {
            DAST._IType _1459___mcc_h29 = _source46.dtor_element;
          } else if (_source46.is_Map) {
            DAST._IType _1460___mcc_h31 = _source46.dtor_key;
            DAST._IType _1461___mcc_h32 = _source46.dtor_value;
          } else if (_source46.is_SetBuilder) {
            DAST._IType _1462___mcc_h35 = _source46.dtor_element;
          } else if (_source46.is_MapBuilder) {
            DAST._IType _1463___mcc_h37 = _source46.dtor_key;
            DAST._IType _1464___mcc_h38 = _source46.dtor_value;
          } else if (_source46.is_Arrow) {
            Dafny.ISequence<DAST._IType> _1465___mcc_h41 = _source46.dtor_args;
            DAST._IType _1466___mcc_h42 = _source46.dtor_result;
          } else if (_source46.is_Primitive) {
            DAST._IPrimitive _1467___mcc_h45 = _source46.dtor_Primitive_a0;
          } else if (_source46.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1468___mcc_h47 = _source46.dtor_Passthrough_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _1469___mcc_h49 = _source46.dtor_TypeArg_a0;
          }
          _1436_i = (_1436_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1470_d;
      _1470_d = RAST.Impl.create_ImplFor(_1414_sConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1430_typeParamsAsTypes), _1415_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1471_defaultImpl;
      _1471_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1470_d));
      RAST._IImpl _1472_p;
      _1472_p = RAST.Impl.create_ImplFor(_1414_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1430_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), ((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1473_printImpl;
      _1473_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1472_p));
      RAST._IImpl _1474_pp;
      _1474_pp = RAST.Impl.create_ImplFor(_1413_sTypeParams, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1430_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.Self)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1475_ptrPartialEqImpl;
      _1475_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1474_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1471_defaultImpl), _1473_printImpl), _1475_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1476_typeParamsSet;
      _1476_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._IType> _1477_typeParams;
      _1477_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1478_tpI;
      _1478_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1478_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._IType _1479_tp;
          _1479_tp = ((t).dtor_typeParams).Select(_1478_tpI);
          _1476_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1476_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1479_tp));
          RAST._IType _1480_genTp;
          RAST._IType _out36;
          _out36 = (this).GenType(_1479_tp, false, false);
          _1480_genTp = _out36;
          _1477_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1477_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1480_genTp));
          _1478_tpI = (_1478_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1481_fullPath;
      _1481_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1482_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1483___v31;
      Dafny.ISequence<RAST._IImplMember> _out37;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out38;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1481_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1481_fullPath)), _1476_typeParamsSet, out _out37, out _out38);
      _1482_implBody = _out37;
      _1483___v31 = _out38;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(Dafny.Sequence<RAST._ITypeParam>.FromElements(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((t).dtor_name)), _1477_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1482_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1484_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1485_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1486_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1487_whereConstraints;
      Dafny.ISet<DAST._IType> _out39;
      Dafny.ISequence<RAST._ITypeParam> _out40;
      Dafny.ISequence<RAST._ITypeParam> _out41;
      Dafny.ISequence<Dafny.Rune> _out42;
      (this).GenTypeParameters((c).dtor_typeParams, out _out39, out _out40, out _out41, out _out42);
      _1484_typeParamsSet = _out39;
      _1485_sTypeParams = _out40;
      _1486_sConstrainedTypeParams = _out41;
      _1487_whereConstraints = _out42;
      Dafny.ISequence<RAST._IType> _1488_typeParamsAsTypes;
      _1488_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1489_t) => {
        return RAST.__default.RawType((_1489_t).dtor_content);
      })), _1485_sTypeParams);
      Dafny.ISequence<Dafny.Rune> _1490_constrainedTypeParams;
      _1490_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1486_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1491_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source48 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      if (_source48.is_None) {
        RAST._IType _out43;
        _out43 = (this).GenType((c).dtor_base, false, false);
        _1491_underlyingType = _out43;
      } else {
        RAST._IType _1492___mcc_h0 = _source48.dtor_value;
        RAST._IType _1493_v = _1492___mcc_h0;
        _1491_underlyingType = _1493_v;
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), DCOMP.__default.escapeIdent((c).dtor_name), _1485_sTypeParams, RAST.Formals.create_NamelessFormals(Dafny.Sequence<RAST._INamelessFormal>.FromElements(RAST.NamelessFormal.create(RAST.Visibility.create_PUB(), _1491_underlyingType))))));
      Dafny.ISequence<Dafny.Rune> _1494_fnBody;
      _1494_fnBody = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Std.Wrappers._IOption<DAST._IExpression> _source49 = (c).dtor_witnessExpr;
      if (_source49.is_None) {
        {
          _1494_fnBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1494_fnBody, DCOMP.__default.escapeIdent((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(::std::default::Default::default())"));
        }
      } else {
        DAST._IExpression _1495___mcc_h1 = _source49.dtor_value;
        DAST._IExpression _1496_e = _1495___mcc_h1;
        {
          RAST._IExpr _1497_eStr;
          DCOMP._IOwnership _1498___v32;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1499___v33;
          RAST._IExpr _out44;
          DCOMP._IOwnership _out45;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out46;
          (this).GenExpr(_1496_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out44, out _out45, out _out46);
          _1497_eStr = _out44;
          _1498___v32 = _out45;
          _1499___v33 = _out46;
          _1494_fnBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1494_fnBody, DCOMP.__default.escapeIdent((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1497_eStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
        }
      }
      RAST._IImplMember _1500_body;
      _1500_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(_1494_fnBody))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1486_sConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1488_typeParamsAsTypes), _1487_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1500_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1486_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1488_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1486_sConstrainedTypeParams, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1488_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1491_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&Self::Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1501_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1502_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1503_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1504_whereConstraints;
      Dafny.ISet<DAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParam> _out48;
      Dafny.ISequence<RAST._ITypeParam> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1501_typeParamsSet = _out47;
      _1502_sTypeParams = _out48;
      _1503_sConstrainedTypeParams = _out49;
      _1504_whereConstraints = _out50;
      Dafny.ISequence<RAST._IType> _1505_typeParamsAsTypes;
      _1505_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1506_t) => {
        return RAST.__default.RawType((_1506_t).dtor_content);
      })), _1502_sTypeParams);
      Dafny.ISequence<Dafny.Rune> _1507_constrainedTypeParams;
      _1507_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1503_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.IND, DCOMP.__default.IND));
      Dafny.ISequence<RAST._IEnumCase> _1508_ctors;
      _1508_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _1509_i;
      _1509_i = BigInteger.Zero;
      while ((_1509_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1510_ctor;
        _1510_ctor = ((c).dtor_ctors).Select(_1509_i);
        Dafny.ISequence<RAST._IFormal> _1511_ctorArgs;
        _1511_ctorArgs = Dafny.Sequence<RAST._IFormal>.FromElements();
        BigInteger _1512_j;
        _1512_j = BigInteger.Zero;
        while ((_1512_j) < (new BigInteger(((_1510_ctor).dtor_args).Count))) {
          DAST._IFormal _1513_formal;
          _1513_formal = ((_1510_ctor).dtor_args).Select(_1512_j);
          RAST._IType _1514_formalType;
          RAST._IType _out51;
          _out51 = (this).GenType((_1513_formal).dtor_typ, false, false);
          _1514_formalType = _out51;
          if ((c).dtor_isCo) {
            _1511_ctorArgs = Dafny.Sequence<RAST._IFormal>.Concat(_1511_ctorArgs, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1513_formal).dtor_name), RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1514_formalType)))));
          } else {
            _1511_ctorArgs = Dafny.Sequence<RAST._IFormal>.Concat(_1511_ctorArgs, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1513_formal).dtor_name), _1514_formalType)));
          }
          _1512_j = (_1512_j) + (BigInteger.One);
        }
        _1508_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1508_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeIdent((_1510_ctor).dtor_name), RAST.Formals.create_NamedFormals(_1511_ctorArgs))));
        _1509_i = (_1509_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1515_selfPath;
      _1515_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1516_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1517_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out52;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out53;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(_1515_selfPath)), _1501_typeParamsSet, out _out52, out _out53);
      _1516_implBodyRaw = _out52;
      _1517_traitBodies = _out53;
      Dafny.ISequence<RAST._IImplMember> _1518_implBody;
      _1518_implBody = _1516_implBodyRaw;
      _1509_i = BigInteger.Zero;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1519_emittedFields;
      _1519_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      while ((_1509_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1520_ctor;
        _1520_ctor = ((c).dtor_ctors).Select(_1509_i);
        BigInteger _1521_j;
        _1521_j = BigInteger.Zero;
        while ((_1521_j) < (new BigInteger(((_1520_ctor).dtor_args).Count))) {
          DAST._IFormal _1522_formal;
          _1522_formal = ((_1520_ctor).dtor_args).Select(_1521_j);
          if (!((_1519_emittedFields).Contains((_1522_formal).dtor_name))) {
            _1519_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1519_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1522_formal).dtor_name));
            RAST._IType _1523_formalType;
            RAST._IType _out54;
            _out54 = (this).GenType((_1522_formal).dtor_typ, false, false);
            _1523_formalType = _out54;
            Dafny.ISequence<RAST._IMatchCase> _1524_cases;
            _1524_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _1525_k;
            _1525_k = BigInteger.Zero;
            while ((_1525_k) < (new BigInteger(((c).dtor_ctors).Count))) {
              DAST._IDatatypeCtor _1526_ctor2;
              _1526_ctor2 = ((c).dtor_ctors).Select(_1525_k);
              Dafny.ISequence<Dafny.Rune> _1527_pattern;
              _1527_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent((_1526_ctor2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              Dafny.ISequence<Dafny.Rune> _1528_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              BigInteger _1529_l;
              _1529_l = BigInteger.Zero;
              bool _1530_hasMatchingField;
              _1530_hasMatchingField = false;
              while ((_1529_l) < (new BigInteger(((_1526_ctor2).dtor_args).Count))) {
                DAST._IFormal _1531_formal2;
                _1531_formal2 = ((_1526_ctor2).dtor_args).Select(_1529_l);
                if (((_1522_formal).dtor_name).Equals((_1531_formal2).dtor_name)) {
                  _1530_hasMatchingField = true;
                }
                _1527_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1527_pattern, DCOMP.__default.escapeIdent((_1531_formal2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _1529_l = (_1529_l) + (BigInteger.One);
              }
              _1527_pattern = Dafny.Sequence<Dafny.Rune>.Concat(_1527_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              if (_1530_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _1528_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), DCOMP.__default.escapeIdent((_1522_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1528_rhs = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((_1522_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1528_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1532_ctorMatch;
              _1532_ctorMatch = RAST.MatchCase.create(_1527_pattern, RAST.Expr.create_RawExpr(_1528_rhs));
              _1524_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1524_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1532_ctorMatch));
              _1525_k = (_1525_k) + (BigInteger.One);
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1524_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1524_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1533_methodBody;
            _1533_methodBody = RAST.Expr.create_Match(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")), _1524_cases);
            _1518_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1518_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(DCOMP.__default.escapeIdent((_1522_formal).dtor_name), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1523_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1533_methodBody)))));
          }
          _1521_j = (_1521_j) + (BigInteger.One);
        }
        _1509_i = (_1509_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _1534_typeI;
        _1534_typeI = BigInteger.Zero;
        Dafny.ISequence<RAST._IType> _1535_types;
        _1535_types = Dafny.Sequence<RAST._IType>.FromElements();
        while ((_1534_typeI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          RAST._IType _1536_genTp;
          RAST._IType _out55;
          _out55 = (this).GenType(((c).dtor_typeParams).Select(_1534_typeI), false, false);
          _1536_genTp = _out55;
          _1535_types = Dafny.Sequence<RAST._IType>.Concat(_1535_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData::")), Dafny.Sequence<RAST._IType>.FromElements(_1536_genTp))));
          _1534_typeI = (_1534_typeI) + (BigInteger.One);
        }
        _1508_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1508_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Formals.create_NamelessFormals(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessFormal>(((System.Func<RAST._IType, RAST._INamelessFormal>)((_1537_tpe) => {
  return RAST.NamelessFormal.create(RAST.Visibility.create_PRIV(), _1537_tpe);
})), _1535_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1538_enumBody;
      _1538_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq)]")), DCOMP.__default.escapeIdent((c).dtor_name), _1502_sTypeParams, _1508_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1503_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1505_typeParamsAsTypes), _1504_whereConstraints, _1518_implBody)));
      _1509_i = BigInteger.Zero;
      Dafny.ISequence<RAST._IMatchCase> _1539_printImplBodyCases;
      _1539_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      while ((_1509_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1540_ctor;
        _1540_ctor = ((c).dtor_ctors).Select(_1509_i);
        Dafny.ISequence<Dafny.Rune> _1541_ctorMatch;
        _1541_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((_1540_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _1542_modulePrefix;
        _1542_modulePrefix = (((((c).dtor_enclosingModule)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(((c).dtor_enclosingModule), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        RAST._IExpr _1543_printRhs;
        _1543_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1542_modulePrefix), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent((_1540_ctor).dtor_name)), (((_1540_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        BigInteger _1544_j;
        _1544_j = BigInteger.Zero;
        while ((_1544_j) < (new BigInteger(((_1540_ctor).dtor_args).Count))) {
          DAST._IFormal _1545_formal;
          _1545_formal = ((_1540_ctor).dtor_args).Select(_1544_j);
          _1541_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1541_ctorMatch, DCOMP.__default.escapeIdent((_1545_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1544_j).Sign == 1) {
            _1543_printRhs = (_1543_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1543_printRhs = (_1543_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), DCOMP.__default.escapeIdent((_1545_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
          _1544_j = (_1544_j) + (BigInteger.One);
        }
        _1541_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_1541_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_1540_ctor).dtor_hasAnyArgs) {
          _1543_printRhs = (_1543_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1543_printRhs = (_1543_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1539_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1539_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1541_ctorMatch), RAST.Expr.create_Block(_1543_printRhs))));
        _1509_i = (_1509_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1539_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1539_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      RAST._IExpr _1546_printImplBody;
      _1546_printImplBody = RAST.Expr.create_Match(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")), _1539_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1547_printImpl;
      _1547_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1503_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1505_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1546_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1548_defaultImpl;
      _1548_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        _1509_i = BigInteger.Zero;
        Dafny.ISequence<Dafny.Rune> _1549_structName;
        _1549_structName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1550_structAssignments;
        _1550_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        while ((_1509_i) < (new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count))) {
          DAST._IFormal _1551_formal;
          _1551_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1509_i);
          _1550_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1550_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent((_1551_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
          _1509_i = (_1509_i) + (BigInteger.One);
        }
        Dafny.ISequence<RAST._ITypeParam> _1552_defaultConstrainedTypeParams;
        _1552_defaultConstrainedTypeParams = RAST.TypeParam.AddConstraintsMultiple(_1502_sTypeParams, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        _1548_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1552_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1505_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1549_structName, _1550_structAssignments))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1538_enumBody, _1547_printImpl), _1548_defaultImpl);
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
        BigInteger _1553_i;
        _1553_i = BigInteger.Zero;
        while ((_1553_i) < (new BigInteger((p).Count))) {
          if ((_1553_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeIdent(((p).Select(_1553_i))));
          _1553_i = (_1553_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1554_i;
        _1554_i = BigInteger.Zero;
        while ((_1554_i) < (new BigInteger((args).Count))) {
          RAST._IType _1555_genTp;
          RAST._IType _out56;
          _out56 = (this).GenType((args).Select(_1554_i), inBinding, inFn);
          _1555_genTp = _out56;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1555_genTp));
          _1554_i = (_1554_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public RAST._IType GenType(DAST._IType c, bool inBinding, bool inFn)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source50 = c;
      if (_source50.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1556___mcc_h0 = _source50.dtor_Path_a0;
        Dafny.ISequence<DAST._IType> _1557___mcc_h1 = _source50.dtor_typeArgs;
        DAST._IResolvedType _1558___mcc_h2 = _source50.dtor_resolved;
        DAST._IResolvedType _1559_resolved = _1558___mcc_h2;
        Dafny.ISequence<DAST._IType> _1560_args = _1557___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1561_p = _1556___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _1562_t;
          Dafny.ISequence<Dafny.Rune> _out57;
          _out57 = DCOMP.COMP.GenPath(_1561_p);
          _1562_t = _out57;
          s = RAST.Type.create_TIdentifier(_1562_t);
          Dafny.ISequence<RAST._IType> _1563_typeArgs;
          Dafny.ISequence<RAST._IType> _out58;
          _out58 = (this).GenTypeArgs(_1560_args, inBinding, inFn);
          _1563_typeArgs = _out58;
          s = RAST.Type.create_TypeApp(s, _1563_typeArgs);
          DAST._IResolvedType _source51 = _1559_resolved;
          if (_source51.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1564___mcc_h21 = _source51.dtor_path;
            {
              s = RAST.__default.Rc(s);
            }
          } else if (_source51.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1565___mcc_h22 = _source51.dtor_path;
            {
              if ((_1561_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
            DAST._IType _1566___mcc_h23 = _source51.dtor_baseType;
            DAST._INewtypeRange _1567___mcc_h24 = _source51.dtor_range;
            bool _1568___mcc_h25 = _source51.dtor_erase;
            bool _1569_erased = _1568___mcc_h25;
            DAST._INewtypeRange _1570_range = _1567___mcc_h24;
            DAST._IType _1571_t = _1566___mcc_h23;
            {
              if (_1569_erased) {
                Std.Wrappers._IOption<RAST._IType> _source52 = DCOMP.COMP.NewtypeToRustType(_1571_t, _1570_range);
                if (_source52.is_None) {
                } else {
                  RAST._IType _1572___mcc_h26 = _source52.dtor_value;
                  RAST._IType _1573_v = _1572___mcc_h26;
                  s = _1573_v;
                }
              }
            }
          }
        }
      } else if (_source50.is_Nullable) {
        DAST._IType _1574___mcc_h3 = _source50.dtor_Nullable_a0;
        DAST._IType _1575_inner = _1574___mcc_h3;
        {
          RAST._IType _1576_innerExpr;
          RAST._IType _out59;
          _out59 = (this).GenType(_1575_inner, inBinding, inFn);
          _1576_innerExpr = _out59;
          s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1576_innerExpr));
        }
      } else if (_source50.is_Tuple) {
        Dafny.ISequence<DAST._IType> _1577___mcc_h4 = _source50.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IType> _1578_types = _1577___mcc_h4;
        {
          Dafny.ISequence<RAST._IType> _1579_args;
          _1579_args = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _1580_i;
          _1580_i = BigInteger.Zero;
          while ((_1580_i) < (new BigInteger((_1578_types).Count))) {
            RAST._IType _1581_generated;
            RAST._IType _out60;
            _out60 = (this).GenType((_1578_types).Select(_1580_i), inBinding, inFn);
            _1581_generated = _out60;
            _1579_args = Dafny.Sequence<RAST._IType>.Concat(_1579_args, Dafny.Sequence<RAST._IType>.FromElements(_1581_generated));
            _1580_i = (_1580_i) + (BigInteger.One);
          }
          s = RAST.Type.create_TupleType(_1579_args);
        }
      } else if (_source50.is_Array) {
        DAST._IType _1582___mcc_h5 = _source50.dtor_element;
        BigInteger _1583___mcc_h6 = _source50.dtor_dims;
        BigInteger _1584_dims = _1583___mcc_h6;
        DAST._IType _1585_element = _1582___mcc_h5;
        {
          RAST._IType _1586_elem;
          RAST._IType _out61;
          _out61 = (this).GenType(_1585_element, inBinding, inFn);
          _1586_elem = _out61;
          s = _1586_elem;
          BigInteger _1587_i;
          _1587_i = BigInteger.Zero;
          while ((_1587_i) < (_1584_dims)) {
            s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
            _1587_i = (_1587_i) + (BigInteger.One);
          }
        }
      } else if (_source50.is_Seq) {
        DAST._IType _1588___mcc_h7 = _source50.dtor_element;
        DAST._IType _1589_element = _1588___mcc_h7;
        {
          RAST._IType _1590_elem;
          RAST._IType _out62;
          _out62 = (this).GenType(_1589_element, inBinding, inFn);
          _1590_elem = _out62;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1590_elem));
        }
      } else if (_source50.is_Set) {
        DAST._IType _1591___mcc_h8 = _source50.dtor_element;
        DAST._IType _1592_element = _1591___mcc_h8;
        {
          RAST._IType _1593_elem;
          RAST._IType _out63;
          _out63 = (this).GenType(_1592_element, inBinding, inFn);
          _1593_elem = _out63;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1593_elem));
        }
      } else if (_source50.is_Multiset) {
        DAST._IType _1594___mcc_h9 = _source50.dtor_element;
        DAST._IType _1595_element = _1594___mcc_h9;
        {
          RAST._IType _1596_elem;
          RAST._IType _out64;
          _out64 = (this).GenType(_1595_element, inBinding, inFn);
          _1596_elem = _out64;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1596_elem));
        }
      } else if (_source50.is_Map) {
        DAST._IType _1597___mcc_h10 = _source50.dtor_key;
        DAST._IType _1598___mcc_h11 = _source50.dtor_value;
        DAST._IType _1599_value = _1598___mcc_h11;
        DAST._IType _1600_key = _1597___mcc_h10;
        {
          RAST._IType _1601_keyType;
          RAST._IType _out65;
          _out65 = (this).GenType(_1600_key, inBinding, inFn);
          _1601_keyType = _out65;
          RAST._IType _1602_valueType;
          RAST._IType _out66;
          _out66 = (this).GenType(_1599_value, inBinding, inFn);
          _1602_valueType = _out66;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1601_keyType, _1602_valueType));
        }
      } else if (_source50.is_SetBuilder) {
        DAST._IType _1603___mcc_h12 = _source50.dtor_element;
        DAST._IType _1604_elem = _1603___mcc_h12;
        {
          RAST._IType _1605_elemType;
          RAST._IType _out67;
          _out67 = (this).GenType(_1604_elem, inBinding, inFn);
          _1605_elemType = _out67;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1605_elemType));
        }
      } else if (_source50.is_MapBuilder) {
        DAST._IType _1606___mcc_h13 = _source50.dtor_key;
        DAST._IType _1607___mcc_h14 = _source50.dtor_value;
        DAST._IType _1608_value = _1607___mcc_h14;
        DAST._IType _1609_key = _1606___mcc_h13;
        {
          RAST._IType _1610_keyType;
          RAST._IType _out68;
          _out68 = (this).GenType(_1609_key, inBinding, inFn);
          _1610_keyType = _out68;
          RAST._IType _1611_valueType;
          RAST._IType _out69;
          _out69 = (this).GenType(_1608_value, inBinding, inFn);
          _1611_valueType = _out69;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1610_keyType, _1611_valueType));
        }
      } else if (_source50.is_Arrow) {
        Dafny.ISequence<DAST._IType> _1612___mcc_h15 = _source50.dtor_args;
        DAST._IType _1613___mcc_h16 = _source50.dtor_result;
        DAST._IType _1614_result = _1613___mcc_h16;
        Dafny.ISequence<DAST._IType> _1615_args = _1612___mcc_h15;
        {
          Dafny.ISequence<RAST._IType> _1616_argTypes;
          _1616_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _1617_i;
          _1617_i = BigInteger.Zero;
          while ((_1617_i) < (new BigInteger((_1615_args).Count))) {
            RAST._IType _1618_generated;
            RAST._IType _out70;
            _out70 = (this).GenType((_1615_args).Select(_1617_i), inBinding, true);
            _1618_generated = _out70;
            _1616_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1616_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1618_generated)));
            _1617_i = (_1617_i) + (BigInteger.One);
          }
          RAST._IType _1619_resultType;
          RAST._IType _out71;
          _out71 = (this).GenType(_1614_result, inBinding, (inFn) || (inBinding));
          _1619_resultType = _out71;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("FunctionWrapper")), Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_FnType(_1616_argTypes, RAST.Type.create_IntersectionType(_1619_resultType, RAST.__default.StaticTrait))));
        }
      } else if (_source50.is_Primitive) {
        DAST._IPrimitive _1620___mcc_h17 = _source50.dtor_Primitive_a0;
        DAST._IPrimitive _1621_p = _1620___mcc_h17;
        {
          DAST._IPrimitive _source53 = _1621_p;
          if (_source53.is_Int) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
          } else if (_source53.is_Real) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
          } else if (_source53.is_String) {
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
          } else if (_source53.is_Bool) {
            s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool"));
          } else {
            s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
          }
        }
      } else if (_source50.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _1622___mcc_h18 = _source50.dtor_Passthrough_a0;
        Dafny.ISequence<Dafny.Rune> _1623_v = _1622___mcc_h18;
        s = RAST.__default.RawType(_1623_v);
      } else {
        Dafny.ISequence<Dafny.Rune> _1624___mcc_h19 = _source50.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _source54 = _1624___mcc_h19;
        Dafny.ISequence<Dafny.Rune> _1625___mcc_h20 = _source54;
        Dafny.ISequence<Dafny.Rune> _1626_name = _1625___mcc_h20;
        s = RAST.__default.RawType(DCOMP.__default.escapeIdent(_1626_name));
      }
      return s;
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _1627_i;
      _1627_i = BigInteger.Zero;
      while ((_1627_i) < (new BigInteger((body).Count))) {
        DAST._IMethod _source55 = (body).Select(_1627_i);
        DAST._IMethod _1628___mcc_h0 = _source55;
        DAST._IMethod _1629_m = _1628___mcc_h0;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source56 = (_1629_m).dtor_overridingPath;
          if (_source56.is_None) {
            {
              RAST._IImplMember _1630_generated;
              RAST._IImplMember _out72;
              _out72 = (this).GenMethod(_1629_m, forTrait, enclosingType, enclosingTypeParams);
              _1630_generated = _out72;
              s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1630_generated));
            }
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1631___mcc_h1 = _source56.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1632_p = _1631___mcc_h1;
            {
              Dafny.ISequence<RAST._IImplMember> _1633_existing;
              _1633_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
              if ((traitBodies).Contains(_1632_p)) {
                _1633_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1632_p);
              }
              RAST._IImplMember _1634_genMethod;
              RAST._IImplMember _out73;
              _out73 = (this).GenMethod(_1629_m, true, enclosingType, enclosingTypeParams);
              _1634_genMethod = _out73;
              _1633_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1633_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1634_genMethod));
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1632_p, _1633_existing)));
            }
          }
        }
        _1627_i = (_1627_i) + (BigInteger.One);
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _1635_i;
      _1635_i = BigInteger.Zero;
      while ((_1635_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _1636_param;
        _1636_param = (@params).Select(_1635_i);
        RAST._IType _1637_paramType;
        RAST._IType _out74;
        _out74 = (this).GenType((_1636_param).dtor_typ, false, false);
        _1637_paramType = _out74;
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1636_param).dtor_name), RAST.Type.create_Borrowed(_1637_paramType))));
        _1635_i = (_1635_i) + (BigInteger.One);
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1638_params;
      Dafny.ISequence<RAST._IFormal> _out75;
      _out75 = (this).GenParams((m).dtor_params);
      _1638_params = _out75;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1639_paramNames;
      _1639_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1640_paramI;
      _1640_paramI = BigInteger.Zero;
      while ((_1640_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _1639_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1639_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_1640_paramI)).dtor_name));
        _1640_paramI = (_1640_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _1638_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), _1638_params);
        } else {
          RAST._IType _1641_tpe;
          RAST._IType _out76;
          _out76 = (this).GenType(enclosingType, false, false);
          _1641_tpe = _out76;
          _1638_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.Type.create_Borrowed(_1641_tpe))), _1638_params);
        }
      }
      Dafny.ISequence<RAST._IType> _1642_retTypeArgs;
      _1642_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1643_typeI;
      _1643_typeI = BigInteger.Zero;
      while ((_1643_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1644_typeExpr;
        RAST._IType _out77;
        _out77 = (this).GenType(((m).dtor_outTypes).Select(_1643_typeI), false, false);
        _1644_typeExpr = _out77;
        _1642_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1642_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1644_typeExpr));
        _1643_typeI = (_1643_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1645_visibility;
      _1645_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<Dafny.Rune> _1646_fnName;
      _1646_fnName = DCOMP.__default.escapeIdent((m).dtor_name);
      Dafny.ISequence<DAST._IType> _1647_typeParamsFiltered;
      _1647_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _1648_typeParamI;
      _1648_typeParamI = BigInteger.Zero;
      while ((_1648_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _1649_typeParam;
        _1649_typeParam = ((m).dtor_typeParams).Select(_1648_typeParamI);
        if (!((enclosingTypeParams).Contains(_1649_typeParam))) {
          _1647_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_1647_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_1649_typeParam));
        }
        _1648_typeParamI = (_1648_typeParamI) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.Rune> _1650_whereClauses;
      _1650_whereClauses = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Dafny.ISequence<RAST._ITypeParam> _1651_typeParams;
      _1651_typeParams = Dafny.Sequence<RAST._ITypeParam>.FromElements();
      if ((new BigInteger((_1647_typeParamsFiltered).Count)).Sign == 1) {
        _1650_whereClauses = Dafny.Sequence<Dafny.Rune>.Concat(_1650_whereClauses, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" where "));
        BigInteger _1652_i;
        _1652_i = BigInteger.Zero;
        while ((_1652_i) < (new BigInteger((_1647_typeParamsFiltered).Count))) {
          RAST._IType _1653_typeExpr;
          RAST._IType _out78;
          _out78 = (this).GenType((_1647_typeParamsFiltered).Select(_1652_i), false, false);
          _1653_typeExpr = _out78;
          _1651_typeParams = Dafny.Sequence<RAST._ITypeParam>.Concat(_1651_typeParams, Dafny.Sequence<RAST._ITypeParam>.FromElements(RAST.TypeParam.create((_1653_typeExpr)._ToString(DCOMP.__default.IND), Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.CloneTrait, RAST.__default.DafnyPrintTrait, RAST.__default.DefaultTrait, RAST.__default.StaticTrait))));
          _1652_i = (_1652_i) + (BigInteger.One);
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1654_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1655_earlyReturn;
        _1655_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source57 = (m).dtor_outVars;
        if (_source57.is_None) {
        } else {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1656___mcc_h0 = _source57.dtor_value;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1657_outVars = _1656___mcc_h0;
          {
            Dafny.ISequence<RAST._IExpr> _1658_tupleArgs;
            _1658_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _1659_outI;
            _1659_outI = BigInteger.Zero;
            while ((_1659_outI) < (new BigInteger((_1657_outVars).Count))) {
              Dafny.ISequence<Dafny.Rune> _1660_outVar;
              _1660_outVar = (_1657_outVars).Select(_1659_outI);
              _1658_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1658_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent((_1660_outVar)))));
              _1659_outI = (_1659_outI) + (BigInteger.One);
            }
            _1655_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1658_tupleArgs)));
          }
        }
        RAST._IExpr _1661_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1662___v36;
        RAST._IExpr _out79;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out80;
        (this).GenStmts((m).dtor_body, (((m).dtor_isStatic) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))), _1639_paramNames, true, _1655_earlyReturn, out _out79, out _out80);
        _1661_body = _out79;
        _1662___v36 = _out80;
        _1654_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some(_1661_body);
      } else {
        _1654_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1645_visibility, RAST.Fn.create(_1646_fnName, _1651_typeParams, _1638_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1642_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1642_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1642_retTypeArgs)))), _1650_whereClauses, _1654_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1663_declarations;
      _1663_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1664_i;
      _1664_i = BigInteger.Zero;
      while ((_1664_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _1665_stmt;
        _1665_stmt = (stmts).Select(_1664_i);
        RAST._IExpr _1666_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1667_recIdents;
        RAST._IExpr _out81;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out82;
        (this).GenStmt(_1665_stmt, selfIdent, @params, (isLast) && ((_1664_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out81, out _out82);
        _1666_stmtExpr = _out81;
        _1667_recIdents = _out82;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1667_recIdents, _1663_declarations));
        DAST._IStatement _source58 = _1665_stmt;
        if (_source58.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1668___mcc_h0 = _source58.dtor_name;
          DAST._IType _1669___mcc_h1 = _source58.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> _1670___mcc_h2 = _source58.dtor_maybeValue;
          Dafny.ISequence<Dafny.Rune> _1671_name = _1668___mcc_h0;
          {
            _1663_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1663_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1671_name));
          }
        } else if (_source58.is_Assign) {
          DAST._IAssignLhs _1672___mcc_h6 = _source58.dtor_lhs;
          DAST._IExpression _1673___mcc_h7 = _source58.dtor_value;
        } else if (_source58.is_If) {
          DAST._IExpression _1674___mcc_h10 = _source58.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1675___mcc_h11 = _source58.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1676___mcc_h12 = _source58.dtor_els;
        } else if (_source58.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1677___mcc_h16 = _source58.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1678___mcc_h17 = _source58.dtor_body;
        } else if (_source58.is_While) {
          DAST._IExpression _1679___mcc_h20 = _source58.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1680___mcc_h21 = _source58.dtor_body;
        } else if (_source58.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1681___mcc_h24 = _source58.dtor_boundName;
          DAST._IType _1682___mcc_h25 = _source58.dtor_boundType;
          DAST._IExpression _1683___mcc_h26 = _source58.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1684___mcc_h27 = _source58.dtor_body;
        } else if (_source58.is_Call) {
          DAST._IExpression _1685___mcc_h32 = _source58.dtor_on;
          DAST._ICallName _1686___mcc_h33 = _source58.dtor_callName;
          Dafny.ISequence<DAST._IType> _1687___mcc_h34 = _source58.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1688___mcc_h35 = _source58.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1689___mcc_h36 = _source58.dtor_outs;
        } else if (_source58.is_Return) {
          DAST._IExpression _1690___mcc_h42 = _source58.dtor_expr;
        } else if (_source58.is_EarlyReturn) {
        } else if (_source58.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1691___mcc_h44 = _source58.dtor_toLabel;
        } else if (_source58.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1692___mcc_h46 = _source58.dtor_body;
        } else if (_source58.is_JumpTailCallStart) {
        } else if (_source58.is_Halt) {
        } else {
          DAST._IExpression _1693___mcc_h48 = _source58.dtor_Print_a0;
        }
        generated = (generated).Then(_1666_stmtExpr);
        _1664_i = (_1664_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, Dafny.ISequence<Dafny.Rune> rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, out Dafny.ISequence<Dafny.Rune> generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IAssignLhs _source59 = lhs;
      if (_source59.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _1694___mcc_h0 = _source59.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _source60 = _1694___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _1695___mcc_h1 = _source60;
        Dafny.ISequence<Dafny.Rune> _1696_id = _1695___mcc_h1;
        {
          if ((@params).Contains(_1696_id)) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), DCOMP.__default.escapeIdent(_1696_id));
          } else {
            generated = DCOMP.__default.escapeIdent(_1696_id);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1696_id);
          needsIIFE = false;
        }
      } else if (_source59.is_Select) {
        DAST._IExpression _1697___mcc_h2 = _source59.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _1698___mcc_h3 = _source59.dtor_field;
        Dafny.ISequence<Dafny.Rune> _1699_field = _1698___mcc_h3;
        DAST._IExpression _1700_on = _1697___mcc_h2;
        {
          RAST._IExpr _1701_onExpr;
          DCOMP._IOwnership _1702_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1703_recIdents;
          RAST._IExpr _out83;
          DCOMP._IOwnership _out84;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out85;
          (this).GenExpr(_1700_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out83, out _out84, out _out85);
          _1701_onExpr = _out83;
          _1702_onOwned = _out84;
          _1703_recIdents = _out85;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_1701_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1699_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          readIdents = _1703_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _1704___mcc_h4 = _source59.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1705___mcc_h5 = _source59.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _1706_indices = _1705___mcc_h5;
        DAST._IExpression _1707_on = _1704___mcc_h4;
        {
          RAST._IExpr _1708_onExpr;
          DCOMP._IOwnership _1709_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1710_recIdents;
          RAST._IExpr _out86;
          DCOMP._IOwnership _out87;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out88;
          (this).GenExpr(_1707_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out86, out _out87, out _out88);
          _1708_onExpr = _out86;
          _1709_onOwned = _out87;
          _1710_recIdents = _out88;
          readIdents = _1710_recIdents;
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _1711_i;
          _1711_i = BigInteger.Zero;
          while ((_1711_i) < (new BigInteger((_1706_indices).Count))) {
            RAST._IExpr _1712_idx;
            DCOMP._IOwnership _1713___v40;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1714_recIdentsIdx;
            RAST._IExpr _out89;
            DCOMP._IOwnership _out90;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
            (this).GenExpr((_1706_indices).Select(_1711_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out89, out _out90, out _out91);
            _1712_idx = _out89;
            _1713___v40 = _out90;
            _1714_recIdentsIdx = _out91;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_1711_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_1712_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1714_recIdentsIdx);
            _1711_i = (_1711_i) + (BigInteger.One);
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, (_1708_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _1711_i = BigInteger.Zero;
          while ((_1711_i) < (new BigInteger((_1706_indices).Count))) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_1711_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _1711_i = (_1711_i) + (BigInteger.One);
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
      DAST._IStatement _source61 = stmt;
      if (_source61.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _1715___mcc_h0 = _source61.dtor_name;
        DAST._IType _1716___mcc_h1 = _source61.dtor_typ;
        Std.Wrappers._IOption<DAST._IExpression> _1717___mcc_h2 = _source61.dtor_maybeValue;
        Std.Wrappers._IOption<DAST._IExpression> _source62 = _1717___mcc_h2;
        if (_source62.is_None) {
          DAST._IType _1718_typ = _1716___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _1719_name = _1715___mcc_h0;
          {
            RAST._IType _1720_typeString;
            RAST._IType _out92;
            _out92 = (this).GenType(_1718_typ, true, false);
            _1720_typeString = _out92;
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_1719_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1720_typeString), Std.Wrappers.Option<RAST._IExpr>.create_None());
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else {
          DAST._IExpression _1721___mcc_h3 = _source62.dtor_value;
          DAST._IExpression _1722_expression = _1721___mcc_h3;
          DAST._IType _1723_typ = _1716___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _1724_name = _1715___mcc_h0;
          {
            RAST._IType _1725_typeString;
            RAST._IType _out93;
            _out93 = (this).GenType(_1723_typ, true, false);
            _1725_typeString = _out93;
            RAST._IExpr _1726_expr;
            DCOMP._IOwnership _1727___v41;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1728_recIdents;
            RAST._IExpr _out94;
            DCOMP._IOwnership _out95;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
            (this).GenExpr(_1722_expression, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out94, out _out95, out _out96);
            _1726_expr = _out94;
            _1727___v41 = _out95;
            _1728_recIdents = _out96;
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_1724_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1725_typeString), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1726_expr));
            readIdents = _1728_recIdents;
          }
        }
      } else if (_source61.is_Assign) {
        DAST._IAssignLhs _1729___mcc_h4 = _source61.dtor_lhs;
        DAST._IExpression _1730___mcc_h5 = _source61.dtor_value;
        DAST._IExpression _1731_expression = _1730___mcc_h5;
        DAST._IAssignLhs _1732_lhs = _1729___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _1733_lhsGen;
          bool _1734_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1735_recIdents;
          Dafny.ISequence<Dafny.Rune> _out97;
          bool _out98;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out99;
          (this).GenAssignLhs(_1732_lhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), selfIdent, @params, out _out97, out _out98, out _out99);
          _1733_lhsGen = _out97;
          _1734_needsIIFE = _out98;
          _1735_recIdents = _out99;
          RAST._IExpr _1736_exprGen;
          DCOMP._IOwnership _1737___v42;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1738_exprIdents;
          RAST._IExpr _out100;
          DCOMP._IOwnership _out101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
          (this).GenExpr(_1731_expression, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out100, out _out101, out _out102);
          _1736_exprGen = _out100;
          _1737___v42 = _out101;
          _1738_exprIdents = _out102;
          if (_1734_needsIIFE) {
            generated = RAST.Expr.create_Block(RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1736_exprGen)), RAST.Expr.create_RawExpr(_1733_lhsGen)));
          } else {
            generated = RAST.Expr.create_AssignVar(_1733_lhsGen, _1736_exprGen);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1735_recIdents, _1738_exprIdents);
        }
      } else if (_source61.is_If) {
        DAST._IExpression _1739___mcc_h6 = _source61.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _1740___mcc_h7 = _source61.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _1741___mcc_h8 = _source61.dtor_els;
        Dafny.ISequence<DAST._IStatement> _1742_els = _1741___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _1743_thn = _1740___mcc_h7;
        DAST._IExpression _1744_cond = _1739___mcc_h6;
        {
          RAST._IExpr _1745_cond;
          DCOMP._IOwnership _1746___v43;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_recIdents;
          RAST._IExpr _out103;
          DCOMP._IOwnership _out104;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
          (this).GenExpr(_1744_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out103, out _out104, out _out105);
          _1745_cond = _out103;
          _1746___v43 = _out104;
          _1747_recIdents = _out105;
          Dafny.ISequence<Dafny.Rune> _1748_condString;
          _1748_condString = (_1745_cond)._ToString(DCOMP.__default.IND);
          readIdents = _1747_recIdents;
          RAST._IExpr _1749_thn;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1750_thnIdents;
          RAST._IExpr _out106;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
          (this).GenStmts(_1743_thn, selfIdent, @params, isLast, earlyReturn, out _out106, out _out107);
          _1749_thn = _out106;
          _1750_thnIdents = _out107;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1750_thnIdents);
          RAST._IExpr _1751_els;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1752_elsIdents;
          RAST._IExpr _out108;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out109;
          (this).GenStmts(_1742_els, selfIdent, @params, isLast, earlyReturn, out _out108, out _out109);
          _1751_els = _out108;
          _1752_elsIdents = _out109;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1752_elsIdents);
          generated = RAST.Expr.create_IfExpr(_1745_cond, _1749_thn, _1751_els);
        }
      } else if (_source61.is_Labeled) {
        Dafny.ISequence<Dafny.Rune> _1753___mcc_h9 = _source61.dtor_lbl;
        Dafny.ISequence<DAST._IStatement> _1754___mcc_h10 = _source61.dtor_body;
        Dafny.ISequence<DAST._IStatement> _1755_body = _1754___mcc_h10;
        Dafny.ISequence<Dafny.Rune> _1756_lbl = _1753___mcc_h9;
        {
          RAST._IExpr _1757_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1758_bodyIdents;
          RAST._IExpr _out110;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
          (this).GenStmts(_1755_body, selfIdent, @params, isLast, earlyReturn, out _out110, out _out111);
          _1757_body = _out110;
          _1758_bodyIdents = _out111;
          readIdents = _1758_bodyIdents;
          generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1756_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1757_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
        }
      } else if (_source61.is_While) {
        DAST._IExpression _1759___mcc_h11 = _source61.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _1760___mcc_h12 = _source61.dtor_body;
        Dafny.ISequence<DAST._IStatement> _1761_body = _1760___mcc_h12;
        DAST._IExpression _1762_cond = _1759___mcc_h11;
        {
          RAST._IExpr _1763_cond;
          DCOMP._IOwnership _1764___v44;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1765_recIdents;
          RAST._IExpr _out112;
          DCOMP._IOwnership _out113;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
          (this).GenExpr(_1762_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out112, out _out113, out _out114);
          _1763_cond = _out112;
          _1764___v44 = _out113;
          _1765_recIdents = _out114;
          readIdents = _1765_recIdents;
          RAST._IExpr _1766_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1767_bodyIdents;
          RAST._IExpr _out115;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
          (this).GenStmts(_1761_body, selfIdent, @params, false, earlyReturn, out _out115, out _out116);
          _1766_body = _out115;
          _1767_bodyIdents = _out116;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1767_bodyIdents);
          generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1763_cond), _1766_body);
        }
      } else if (_source61.is_Foreach) {
        Dafny.ISequence<Dafny.Rune> _1768___mcc_h13 = _source61.dtor_boundName;
        DAST._IType _1769___mcc_h14 = _source61.dtor_boundType;
        DAST._IExpression _1770___mcc_h15 = _source61.dtor_over;
        Dafny.ISequence<DAST._IStatement> _1771___mcc_h16 = _source61.dtor_body;
        Dafny.ISequence<DAST._IStatement> _1772_body = _1771___mcc_h16;
        DAST._IExpression _1773_over = _1770___mcc_h15;
        DAST._IType _1774_boundType = _1769___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _1775_boundName = _1768___mcc_h13;
        {
          RAST._IExpr _1776_over;
          DCOMP._IOwnership _1777___v45;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1778_recIdents;
          RAST._IExpr _out117;
          DCOMP._IOwnership _out118;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
          (this).GenExpr(_1773_over, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out117, out _out118, out _out119);
          _1776_over = _out117;
          _1777___v45 = _out118;
          _1778_recIdents = _out119;
          RAST._IType _1779_boundTypeStr;
          RAST._IType _out120;
          _out120 = (this).GenType(_1774_boundType, false, false);
          _1779_boundTypeStr = _out120;
          readIdents = _1778_recIdents;
          RAST._IExpr _1780_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1781_bodyIdents;
          RAST._IExpr _out121;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
          (this).GenStmts(_1772_body, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1775_boundName)), false, earlyReturn, out _out121, out _out122);
          _1780_body = _out121;
          _1781_bodyIdents = _out122;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1781_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1775_boundName));
          generated = RAST.Expr.create_For(DCOMP.__default.escapeIdent(_1775_boundName), _1776_over, _1780_body);
        }
      } else if (_source61.is_Call) {
        DAST._IExpression _1782___mcc_h17 = _source61.dtor_on;
        DAST._ICallName _1783___mcc_h18 = _source61.dtor_callName;
        Dafny.ISequence<DAST._IType> _1784___mcc_h19 = _source61.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _1785___mcc_h20 = _source61.dtor_args;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1786___mcc_h21 = _source61.dtor_outs;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1787_maybeOutVars = _1786___mcc_h21;
        Dafny.ISequence<DAST._IExpression> _1788_args = _1785___mcc_h20;
        Dafny.ISequence<DAST._IType> _1789_typeArgs = _1784___mcc_h19;
        DAST._ICallName _1790_name = _1783___mcc_h18;
        DAST._IExpression _1791_on = _1782___mcc_h17;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _1792_typeArgString;
          _1792_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_1789_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _1793_typeI;
            _1793_typeI = BigInteger.Zero;
            Dafny.ISequence<RAST._IType> _1794_typeArgsR;
            _1794_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
            while ((_1793_typeI) < (new BigInteger((_1789_typeArgs).Count))) {
              RAST._IType _1795_tpe;
              RAST._IType _out123;
              _out123 = (this).GenType((_1789_typeArgs).Select(_1793_typeI), false, false);
              _1795_tpe = _out123;
              _1794_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1794_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1795_tpe));
              _1793_typeI = (_1793_typeI) + (BigInteger.One);
            }
            _1792_typeArgString = (RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1794_typeArgsR))._ToString(DCOMP.__default.IND);
          }
          Dafny.ISequence<Dafny.Rune> _1796_argString;
          _1796_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _1797_i;
          _1797_i = BigInteger.Zero;
          while ((_1797_i) < (new BigInteger((_1788_args).Count))) {
            if ((_1797_i).Sign == 1) {
              _1796_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1796_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IExpr _1798_argExpr;
            DCOMP._IOwnership _1799_ownership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1800_argIdents;
            RAST._IExpr _out124;
            DCOMP._IOwnership _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            (this).GenExpr((_1788_args).Select(_1797_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out124, out _out125, out _out126);
            _1798_argExpr = _out124;
            _1799_ownership = _out125;
            _1800_argIdents = _out126;
            Dafny.ISequence<Dafny.Rune> _1801_argExprString;
            _1801_argExprString = (_1798_argExpr)._ToString(DCOMP.__default.IND);
            _1796_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1796_argString, _1801_argExprString);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1800_argIdents);
            _1797_i = (_1797_i) + (BigInteger.One);
          }
          RAST._IExpr _1802_onExpr;
          DCOMP._IOwnership _1803___v46;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1804_enclosingIdents;
          RAST._IExpr _out127;
          DCOMP._IOwnership _out128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out129;
          (this).GenExpr(_1791_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out127, out _out128, out _out129);
          _1802_onExpr = _out127;
          _1803___v46 = _out128;
          _1804_enclosingIdents = _out129;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1804_enclosingIdents);
          Dafny.ISequence<Dafny.Rune> _1805_enclosingString;
          _1805_enclosingString = (_1802_onExpr)._ToString(DCOMP.__default.IND);
          DAST._IExpression _source63 = _1791_on;
          if (_source63.is_Literal) {
            DAST._ILiteral _1806___mcc_h26 = _source63.dtor_Literal_a0;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _1807___mcc_h28 = _source63.dtor_Ident_a0;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1808___mcc_h30 = _source63.dtor_Companion_a0;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_1805_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source63.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _1809___mcc_h32 = _source63.dtor_Tuple_a0;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1810___mcc_h34 = _source63.dtor_path;
            Dafny.ISequence<DAST._IType> _1811___mcc_h35 = _source63.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _1812___mcc_h36 = _source63.dtor_args;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _1813___mcc_h40 = _source63.dtor_dims;
            DAST._IType _1814___mcc_h41 = _source63.dtor_typ;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1815___mcc_h44 = _source63.dtor_path;
            Dafny.ISequence<DAST._IType> _1816___mcc_h45 = _source63.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _1817___mcc_h46 = _source63.dtor_variant;
            bool _1818___mcc_h47 = _source63.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1819___mcc_h48 = _source63.dtor_contents;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_Convert) {
            DAST._IExpression _1820___mcc_h54 = _source63.dtor_value;
            DAST._IType _1821___mcc_h55 = _source63.dtor_from;
            DAST._IType _1822___mcc_h56 = _source63.dtor_typ;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_SeqConstruct) {
            DAST._IExpression _1823___mcc_h60 = _source63.dtor_length;
            DAST._IExpression _1824___mcc_h61 = _source63.dtor_elem;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _1825___mcc_h64 = _source63.dtor_elements;
            DAST._IType _1826___mcc_h65 = _source63.dtor_typ;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _1827___mcc_h68 = _source63.dtor_elements;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _1828___mcc_h70 = _source63.dtor_elements;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1829___mcc_h72 = _source63.dtor_mapElems;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_MapBuilder) {
            DAST._IType _1830___mcc_h74 = _source63.dtor_keyType;
            DAST._IType _1831___mcc_h75 = _source63.dtor_valueType;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_SeqUpdate) {
            DAST._IExpression _1832___mcc_h78 = _source63.dtor_expr;
            DAST._IExpression _1833___mcc_h79 = _source63.dtor_indexExpr;
            DAST._IExpression _1834___mcc_h80 = _source63.dtor_value;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_MapUpdate) {
            DAST._IExpression _1835___mcc_h84 = _source63.dtor_expr;
            DAST._IExpression _1836___mcc_h85 = _source63.dtor_indexExpr;
            DAST._IExpression _1837___mcc_h86 = _source63.dtor_value;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_SetBuilder) {
            DAST._IType _1838___mcc_h90 = _source63.dtor_elemType;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_ToMultiset) {
            DAST._IExpression _1839___mcc_h92 = _source63.dtor_ToMultiset_a0;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_This) {
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_Ite) {
            DAST._IExpression _1840___mcc_h94 = _source63.dtor_cond;
            DAST._IExpression _1841___mcc_h95 = _source63.dtor_thn;
            DAST._IExpression _1842___mcc_h96 = _source63.dtor_els;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_UnOp) {
            DAST._IUnaryOp _1843___mcc_h100 = _source63.dtor_unOp;
            DAST._IExpression _1844___mcc_h101 = _source63.dtor_expr;
            DAST.Format._IUnaryOpFormat _1845___mcc_h102 = _source63.dtor_format1;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_BinOp) {
            DAST._IBinOp _1846___mcc_h106 = _source63.dtor_op;
            DAST._IExpression _1847___mcc_h107 = _source63.dtor_left;
            DAST._IExpression _1848___mcc_h108 = _source63.dtor_right;
            DAST.Format._IBinaryOpFormat _1849___mcc_h109 = _source63.dtor_format2;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_ArrayLen) {
            DAST._IExpression _1850___mcc_h114 = _source63.dtor_expr;
            BigInteger _1851___mcc_h115 = _source63.dtor_dim;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_MapKeys) {
            DAST._IExpression _1852___mcc_h118 = _source63.dtor_expr;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_MapValues) {
            DAST._IExpression _1853___mcc_h120 = _source63.dtor_expr;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_Select) {
            DAST._IExpression _1854___mcc_h122 = _source63.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _1855___mcc_h123 = _source63.dtor_field;
            bool _1856___mcc_h124 = _source63.dtor_isConstant;
            bool _1857___mcc_h125 = _source63.dtor_onDatatype;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_SelectFn) {
            DAST._IExpression _1858___mcc_h130 = _source63.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _1859___mcc_h131 = _source63.dtor_field;
            bool _1860___mcc_h132 = _source63.dtor_onDatatype;
            bool _1861___mcc_h133 = _source63.dtor_isStatic;
            BigInteger _1862___mcc_h134 = _source63.dtor_arity;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_Index) {
            DAST._IExpression _1863___mcc_h140 = _source63.dtor_expr;
            DAST._ICollKind _1864___mcc_h141 = _source63.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _1865___mcc_h142 = _source63.dtor_indices;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_IndexRange) {
            DAST._IExpression _1866___mcc_h146 = _source63.dtor_expr;
            bool _1867___mcc_h147 = _source63.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _1868___mcc_h148 = _source63.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _1869___mcc_h149 = _source63.dtor_high;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_TupleSelect) {
            DAST._IExpression _1870___mcc_h154 = _source63.dtor_expr;
            BigInteger _1871___mcc_h155 = _source63.dtor_index;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_Call) {
            DAST._IExpression _1872___mcc_h158 = _source63.dtor_on;
            DAST._ICallName _1873___mcc_h159 = _source63.dtor_callName;
            Dafny.ISequence<DAST._IType> _1874___mcc_h160 = _source63.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _1875___mcc_h161 = _source63.dtor_args;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _1876___mcc_h166 = _source63.dtor_params;
            DAST._IType _1877___mcc_h167 = _source63.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _1878___mcc_h168 = _source63.dtor_body;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1879___mcc_h172 = _source63.dtor_values;
            DAST._IType _1880___mcc_h173 = _source63.dtor_retType;
            DAST._IExpression _1881___mcc_h174 = _source63.dtor_expr;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _1882___mcc_h178 = _source63.dtor_name;
            DAST._IType _1883___mcc_h179 = _source63.dtor_typ;
            DAST._IExpression _1884___mcc_h180 = _source63.dtor_value;
            DAST._IExpression _1885___mcc_h181 = _source63.dtor_iifeBody;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_Apply) {
            DAST._IExpression _1886___mcc_h186 = _source63.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _1887___mcc_h187 = _source63.dtor_args;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_TypeTest) {
            DAST._IExpression _1888___mcc_h190 = _source63.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1889___mcc_h191 = _source63.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _1890___mcc_h192 = _source63.dtor_variant;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_InitializationValue) {
            DAST._IType _1891___mcc_h196 = _source63.dtor_typ;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_BoolBoundedPool) {
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_SetBoundedPool) {
            DAST._IExpression _1892___mcc_h198 = _source63.dtor_of;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source63.is_SeqBoundedPool) {
            DAST._IExpression _1893___mcc_h200 = _source63.dtor_of;
            bool _1894___mcc_h201 = _source63.dtor_includeDuplicates;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IExpression _1895___mcc_h204 = _source63.dtor_lo;
            DAST._IExpression _1896___mcc_h205 = _source63.dtor_hi;
            {
              _1805_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1805_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _1897_receiver;
          _1897_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source64 = _1787_maybeOutVars;
          if (_source64.is_None) {
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1898___mcc_h208 = _source64.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1899_outVars = _1898___mcc_h208;
            {
              if ((new BigInteger((_1899_outVars).Count)) > (BigInteger.One)) {
                _1897_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _1900_outI;
              _1900_outI = BigInteger.Zero;
              while ((_1900_outI) < (new BigInteger((_1899_outVars).Count))) {
                if ((_1900_outI).Sign == 1) {
                  _1897_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_1897_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _1901_outVar;
                _1901_outVar = (_1899_outVars).Select(_1900_outI);
                _1897_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_1897_receiver, (_1901_outVar));
                _1900_outI = (_1900_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_1899_outVars).Count)) > (BigInteger.One)) {
                _1897_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_1897_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          }
          Dafny.ISequence<Dafny.Rune> _1902_renderedName;
          _1902_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source65) => {
            if (_source65.is_Name) {
              Dafny.ISequence<Dafny.Rune> _1903___mcc_h209 = _source65.dtor_name;
              Dafny.ISequence<Dafny.Rune> _1904_name = _1903___mcc_h209;
              return DCOMP.__default.escapeIdent(_1904_name);
            } else if (_source65.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source65.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source65.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_1790_name);
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_1897_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_1897_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _1805_enclosingString), _1902_renderedName), _1792_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1796_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");")));
        }
      } else if (_source61.is_Return) {
        DAST._IExpression _1905___mcc_h22 = _source61.dtor_expr;
        DAST._IExpression _1906_expr = _1905___mcc_h22;
        {
          RAST._IExpr _1907_expr;
          DCOMP._IOwnership _1908___v49;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1909_recIdents;
          RAST._IExpr _out130;
          DCOMP._IOwnership _out131;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
          (this).GenExpr(_1906_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out130, out _out131, out _out132);
          _1907_expr = _out130;
          _1908___v49 = _out131;
          _1909_recIdents = _out132;
          readIdents = _1909_recIdents;
          if (isLast) {
            generated = _1907_expr;
          } else {
            generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1907_expr));
          }
        }
      } else if (_source61.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source61.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1910___mcc_h23 = _source61.dtor_toLabel;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1911_toLabel = _1910___mcc_h23;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source66 = _1911_toLabel;
          if (_source66.is_None) {
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _1912___mcc_h210 = _source66.dtor_value;
            Dafny.ISequence<Dafny.Rune> _1913_lbl = _1912___mcc_h210;
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1913_lbl)));
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source61.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _1914___mcc_h24 = _source61.dtor_body;
        Dafny.ISequence<DAST._IStatement> _1915_body = _1914___mcc_h24;
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self.clone()")))));
          }
          BigInteger _1916_paramI;
          _1916_paramI = BigInteger.Zero;
          while ((_1916_paramI) < (new BigInteger((@params).Count))) {
            Dafny.ISequence<Dafny.Rune> _1917_param;
            _1917_param = (@params).Select(_1916_paramI);
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_1917_param), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.Clone(RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent(_1917_param))))));
            _1916_paramI = (_1916_paramI) + (BigInteger.One);
          }
          RAST._IExpr _1918_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1919_bodyIdents;
          RAST._IExpr _out133;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
          (this).GenStmts(_1915_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out133, out _out134);
          _1918_body = _out133;
          _1919_bodyIdents = _out134;
          readIdents = _1919_bodyIdents;
          generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1918_body)));
        }
      } else if (_source61.is_JumpTailCallStart) {
        {
          generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source61.is_Halt) {
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else {
        DAST._IExpression _1920___mcc_h25 = _source61.dtor_Print_a0;
        DAST._IExpression _1921_e = _1920___mcc_h25;
        {
          RAST._IExpr _1922_printedExpr;
          DCOMP._IOwnership _1923_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1924_recIdents;
          RAST._IExpr _out135;
          DCOMP._IOwnership _out136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
          (this).GenExpr(_1921_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out135, out _out136, out _out137);
          _1922_printedExpr = _out135;
          _1923_recOwnership = _out136;
          _1924_recIdents = _out137;
          Dafny.ISequence<Dafny.Rune> _1925_printedExprString;
          _1925_printedExprString = (_1922_printedExpr)._ToString(DCOMP.__default.IND);
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), _1925_printedExprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));")));
          readIdents = _1924_recIdents;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source67 = range;
      if (_source67.is_U8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
      } else if (_source67.is_I8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
      } else if (_source67.is_U16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
      } else if (_source67.is_I16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
      } else if (_source67.is_U32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
      } else if (_source67.is_I32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
      } else if (_source67.is_U64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
      } else if (_source67.is_I64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
      } else if (_source67.is_U128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
      } else if (_source67.is_I128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
      } else if (_source67.is_BigInt) {
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
      DAST._IExpression _source68 = e;
      DAST._ILiteral _1926___mcc_h0 = _source68.dtor_Literal_a0;
      DAST._ILiteral _source69 = _1926___mcc_h0;
      if (_source69.is_BoolLiteral) {
        bool _1927___mcc_h1 = _source69.dtor_BoolLiteral_a0;
        if ((_1927___mcc_h1) == (false)) {
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
      } else if (_source69.is_IntLiteral) {
        Dafny.ISequence<Dafny.Rune> _1928___mcc_h2 = _source69.dtor_IntLiteral_a0;
        DAST._IType _1929___mcc_h3 = _source69.dtor_IntLiteral_a1;
        DAST._IType _1930_t = _1929___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _1931_i = _1928___mcc_h2;
        {
          DAST._IType _source70 = _1930_t;
          if (_source70.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1932___mcc_h100 = _source70.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1933___mcc_h101 = _source70.dtor_typeArgs;
            DAST._IResolvedType _1934___mcc_h102 = _source70.dtor_resolved;
            DAST._IType _1935_o = _1930_t;
            {
              RAST._IType _1936_genType;
              RAST._IType _out144;
              _out144 = (this).GenType(_1935_o, false, false);
              _1936_genType = _out144;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1936_genType);
            }
          } else if (_source70.is_Nullable) {
            DAST._IType _1937___mcc_h106 = _source70.dtor_Nullable_a0;
            DAST._IType _1938_o = _1930_t;
            {
              RAST._IType _1939_genType;
              RAST._IType _out145;
              _out145 = (this).GenType(_1938_o, false, false);
              _1939_genType = _out145;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1939_genType);
            }
          } else if (_source70.is_Tuple) {
            Dafny.ISequence<DAST._IType> _1940___mcc_h108 = _source70.dtor_Tuple_a0;
            DAST._IType _1941_o = _1930_t;
            {
              RAST._IType _1942_genType;
              RAST._IType _out146;
              _out146 = (this).GenType(_1941_o, false, false);
              _1942_genType = _out146;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1942_genType);
            }
          } else if (_source70.is_Array) {
            DAST._IType _1943___mcc_h110 = _source70.dtor_element;
            BigInteger _1944___mcc_h111 = _source70.dtor_dims;
            DAST._IType _1945_o = _1930_t;
            {
              RAST._IType _1946_genType;
              RAST._IType _out147;
              _out147 = (this).GenType(_1945_o, false, false);
              _1946_genType = _out147;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1946_genType);
            }
          } else if (_source70.is_Seq) {
            DAST._IType _1947___mcc_h114 = _source70.dtor_element;
            DAST._IType _1948_o = _1930_t;
            {
              RAST._IType _1949_genType;
              RAST._IType _out148;
              _out148 = (this).GenType(_1948_o, false, false);
              _1949_genType = _out148;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1949_genType);
            }
          } else if (_source70.is_Set) {
            DAST._IType _1950___mcc_h116 = _source70.dtor_element;
            DAST._IType _1951_o = _1930_t;
            {
              RAST._IType _1952_genType;
              RAST._IType _out149;
              _out149 = (this).GenType(_1951_o, false, false);
              _1952_genType = _out149;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1952_genType);
            }
          } else if (_source70.is_Multiset) {
            DAST._IType _1953___mcc_h118 = _source70.dtor_element;
            DAST._IType _1954_o = _1930_t;
            {
              RAST._IType _1955_genType;
              RAST._IType _out150;
              _out150 = (this).GenType(_1954_o, false, false);
              _1955_genType = _out150;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1955_genType);
            }
          } else if (_source70.is_Map) {
            DAST._IType _1956___mcc_h120 = _source70.dtor_key;
            DAST._IType _1957___mcc_h121 = _source70.dtor_value;
            DAST._IType _1958_o = _1930_t;
            {
              RAST._IType _1959_genType;
              RAST._IType _out151;
              _out151 = (this).GenType(_1958_o, false, false);
              _1959_genType = _out151;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1959_genType);
            }
          } else if (_source70.is_SetBuilder) {
            DAST._IType _1960___mcc_h124 = _source70.dtor_element;
            DAST._IType _1961_o = _1930_t;
            {
              RAST._IType _1962_genType;
              RAST._IType _out152;
              _out152 = (this).GenType(_1961_o, false, false);
              _1962_genType = _out152;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1962_genType);
            }
          } else if (_source70.is_MapBuilder) {
            DAST._IType _1963___mcc_h126 = _source70.dtor_key;
            DAST._IType _1964___mcc_h127 = _source70.dtor_value;
            DAST._IType _1965_o = _1930_t;
            {
              RAST._IType _1966_genType;
              RAST._IType _out153;
              _out153 = (this).GenType(_1965_o, false, false);
              _1966_genType = _out153;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1966_genType);
            }
          } else if (_source70.is_Arrow) {
            Dafny.ISequence<DAST._IType> _1967___mcc_h130 = _source70.dtor_args;
            DAST._IType _1968___mcc_h131 = _source70.dtor_result;
            DAST._IType _1969_o = _1930_t;
            {
              RAST._IType _1970_genType;
              RAST._IType _out154;
              _out154 = (this).GenType(_1969_o, false, false);
              _1970_genType = _out154;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1970_genType);
            }
          } else if (_source70.is_Primitive) {
            DAST._IPrimitive _1971___mcc_h134 = _source70.dtor_Primitive_a0;
            DAST._IPrimitive _source71 = _1971___mcc_h134;
            if (_source71.is_Int) {
              {
                if ((new BigInteger((_1931_i).Count)) <= (new BigInteger(4))) {
                  r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(RAST.Expr.create_LiteralInt(_1931_i));
                } else {
                  r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(RAST.Expr.create_LiteralString(_1931_i, true));
                }
              }
            } else if (_source71.is_Real) {
              DAST._IType _1972_o = _1930_t;
              {
                RAST._IType _1973_genType;
                RAST._IType _out155;
                _out155 = (this).GenType(_1972_o, false, false);
                _1973_genType = _out155;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1973_genType);
              }
            } else if (_source71.is_String) {
              DAST._IType _1974_o = _1930_t;
              {
                RAST._IType _1975_genType;
                RAST._IType _out156;
                _out156 = (this).GenType(_1974_o, false, false);
                _1975_genType = _out156;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1975_genType);
              }
            } else if (_source71.is_Bool) {
              DAST._IType _1976_o = _1930_t;
              {
                RAST._IType _1977_genType;
                RAST._IType _out157;
                _out157 = (this).GenType(_1976_o, false, false);
                _1977_genType = _out157;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1977_genType);
              }
            } else {
              DAST._IType _1978_o = _1930_t;
              {
                RAST._IType _1979_genType;
                RAST._IType _out158;
                _out158 = (this).GenType(_1978_o, false, false);
                _1979_genType = _out158;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1979_genType);
              }
            }
          } else if (_source70.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1980___mcc_h136 = _source70.dtor_Passthrough_a0;
            DAST._IType _1981_o = _1930_t;
            {
              RAST._IType _1982_genType;
              RAST._IType _out159;
              _out159 = (this).GenType(_1981_o, false, false);
              _1982_genType = _out159;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1982_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _1983___mcc_h138 = _source70.dtor_TypeArg_a0;
            DAST._IType _1984_o = _1930_t;
            {
              RAST._IType _1985_genType;
              RAST._IType _out160;
              _out160 = (this).GenType(_1984_o, false, false);
              _1985_genType = _out160;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1931_i), _1985_genType);
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
      } else if (_source69.is_DecLiteral) {
        Dafny.ISequence<Dafny.Rune> _1986___mcc_h4 = _source69.dtor_DecLiteral_a0;
        Dafny.ISequence<Dafny.Rune> _1987___mcc_h5 = _source69.dtor_DecLiteral_a1;
        DAST._IType _1988___mcc_h6 = _source69.dtor_DecLiteral_a2;
        DAST._IType _1989_t = _1988___mcc_h6;
        Dafny.ISequence<Dafny.Rune> _1990_d = _1987___mcc_h5;
        Dafny.ISequence<Dafny.Rune> _1991_n = _1986___mcc_h4;
        {
          DAST._IType _source72 = _1989_t;
          if (_source72.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1992___mcc_h140 = _source72.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _1993___mcc_h141 = _source72.dtor_typeArgs;
            DAST._IResolvedType _1994___mcc_h142 = _source72.dtor_resolved;
            DAST._IType _1995_o = _1989_t;
            {
              RAST._IType _1996_genType;
              RAST._IType _out163;
              _out163 = (this).GenType(_1995_o, false, false);
              _1996_genType = _out163;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1996_genType);
            }
          } else if (_source72.is_Nullable) {
            DAST._IType _1997___mcc_h146 = _source72.dtor_Nullable_a0;
            DAST._IType _1998_o = _1989_t;
            {
              RAST._IType _1999_genType;
              RAST._IType _out164;
              _out164 = (this).GenType(_1998_o, false, false);
              _1999_genType = _out164;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1999_genType);
            }
          } else if (_source72.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2000___mcc_h148 = _source72.dtor_Tuple_a0;
            DAST._IType _2001_o = _1989_t;
            {
              RAST._IType _2002_genType;
              RAST._IType _out165;
              _out165 = (this).GenType(_2001_o, false, false);
              _2002_genType = _out165;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2002_genType);
            }
          } else if (_source72.is_Array) {
            DAST._IType _2003___mcc_h150 = _source72.dtor_element;
            BigInteger _2004___mcc_h151 = _source72.dtor_dims;
            DAST._IType _2005_o = _1989_t;
            {
              RAST._IType _2006_genType;
              RAST._IType _out166;
              _out166 = (this).GenType(_2005_o, false, false);
              _2006_genType = _out166;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2006_genType);
            }
          } else if (_source72.is_Seq) {
            DAST._IType _2007___mcc_h154 = _source72.dtor_element;
            DAST._IType _2008_o = _1989_t;
            {
              RAST._IType _2009_genType;
              RAST._IType _out167;
              _out167 = (this).GenType(_2008_o, false, false);
              _2009_genType = _out167;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2009_genType);
            }
          } else if (_source72.is_Set) {
            DAST._IType _2010___mcc_h156 = _source72.dtor_element;
            DAST._IType _2011_o = _1989_t;
            {
              RAST._IType _2012_genType;
              RAST._IType _out168;
              _out168 = (this).GenType(_2011_o, false, false);
              _2012_genType = _out168;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2012_genType);
            }
          } else if (_source72.is_Multiset) {
            DAST._IType _2013___mcc_h158 = _source72.dtor_element;
            DAST._IType _2014_o = _1989_t;
            {
              RAST._IType _2015_genType;
              RAST._IType _out169;
              _out169 = (this).GenType(_2014_o, false, false);
              _2015_genType = _out169;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2015_genType);
            }
          } else if (_source72.is_Map) {
            DAST._IType _2016___mcc_h160 = _source72.dtor_key;
            DAST._IType _2017___mcc_h161 = _source72.dtor_value;
            DAST._IType _2018_o = _1989_t;
            {
              RAST._IType _2019_genType;
              RAST._IType _out170;
              _out170 = (this).GenType(_2018_o, false, false);
              _2019_genType = _out170;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2019_genType);
            }
          } else if (_source72.is_SetBuilder) {
            DAST._IType _2020___mcc_h164 = _source72.dtor_element;
            DAST._IType _2021_o = _1989_t;
            {
              RAST._IType _2022_genType;
              RAST._IType _out171;
              _out171 = (this).GenType(_2021_o, false, false);
              _2022_genType = _out171;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2022_genType);
            }
          } else if (_source72.is_MapBuilder) {
            DAST._IType _2023___mcc_h166 = _source72.dtor_key;
            DAST._IType _2024___mcc_h167 = _source72.dtor_value;
            DAST._IType _2025_o = _1989_t;
            {
              RAST._IType _2026_genType;
              RAST._IType _out172;
              _out172 = (this).GenType(_2025_o, false, false);
              _2026_genType = _out172;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2026_genType);
            }
          } else if (_source72.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2027___mcc_h170 = _source72.dtor_args;
            DAST._IType _2028___mcc_h171 = _source72.dtor_result;
            DAST._IType _2029_o = _1989_t;
            {
              RAST._IType _2030_genType;
              RAST._IType _out173;
              _out173 = (this).GenType(_2029_o, false, false);
              _2030_genType = _out173;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2030_genType);
            }
          } else if (_source72.is_Primitive) {
            DAST._IPrimitive _2031___mcc_h174 = _source72.dtor_Primitive_a0;
            DAST._IPrimitive _source73 = _2031___mcc_h174;
            if (_source73.is_Int) {
              DAST._IType _2032_o = _1989_t;
              {
                RAST._IType _2033_genType;
                RAST._IType _out174;
                _out174 = (this).GenType(_2032_o, false, false);
                _2033_genType = _out174;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2033_genType);
              }
            } else if (_source73.is_Real) {
              {
                r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
              }
            } else if (_source73.is_String) {
              DAST._IType _2034_o = _1989_t;
              {
                RAST._IType _2035_genType;
                RAST._IType _out175;
                _out175 = (this).GenType(_2034_o, false, false);
                _2035_genType = _out175;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2035_genType);
              }
            } else if (_source73.is_Bool) {
              DAST._IType _2036_o = _1989_t;
              {
                RAST._IType _2037_genType;
                RAST._IType _out176;
                _out176 = (this).GenType(_2036_o, false, false);
                _2037_genType = _out176;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2037_genType);
              }
            } else {
              DAST._IType _2038_o = _1989_t;
              {
                RAST._IType _2039_genType;
                RAST._IType _out177;
                _out177 = (this).GenType(_2038_o, false, false);
                _2039_genType = _out177;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2039_genType);
              }
            }
          } else if (_source72.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2040___mcc_h176 = _source72.dtor_Passthrough_a0;
            DAST._IType _2041_o = _1989_t;
            {
              RAST._IType _2042_genType;
              RAST._IType _out178;
              _out178 = (this).GenType(_2041_o, false, false);
              _2042_genType = _out178;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2042_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2043___mcc_h178 = _source72.dtor_TypeArg_a0;
            DAST._IType _2044_o = _1989_t;
            {
              RAST._IType _2045_genType;
              RAST._IType _out179;
              _out179 = (this).GenType(_2044_o, false, false);
              _2045_genType = _out179;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1991_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1990_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2045_genType);
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
      } else if (_source69.is_StringLiteral) {
        Dafny.ISequence<Dafny.Rune> _2046___mcc_h7 = _source69.dtor_StringLiteral_a0;
        Dafny.ISequence<Dafny.Rune> _2047_l = _2046___mcc_h7;
        {
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_of"))).Apply1(RAST.Expr.create_LiteralString(_2047_l, false));
          RAST._IExpr _out182;
          DCOMP._IOwnership _out183;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out182, out _out183);
          r = _out182;
          resultingOwnership = _out183;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source69.is_CharLiteral) {
        Dafny.Rune _2048___mcc_h8 = _source69.dtor_CharLiteral_a0;
        Dafny.Rune _2049_c = _2048___mcc_h8;
        {
          r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_2049_c).Value)));
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
        DAST._IType _2050___mcc_h9 = _source69.dtor_Null_a0;
        DAST._IType _2051_tpe = _2050___mcc_h9;
        {
          RAST._IType _2052_tpeGen;
          RAST._IType _out186;
          _out186 = (this).GenType(_2051_tpe, false, false);
          _2052_tpeGen = _out186;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _2052_tpeGen);
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
      DAST._IBinOp _2053_op = _let_tmp_rhs49.dtor_op;
      DAST._IExpression _2054_lExpr = _let_tmp_rhs49.dtor_left;
      DAST._IExpression _2055_rExpr = _let_tmp_rhs49.dtor_right;
      DAST.Format._IBinaryOpFormat _2056_format = _let_tmp_rhs49.dtor_format2;
      bool _2057_becomesLeftCallsRight;
      _2057_becomesLeftCallsRight = ((System.Func<DAST._IBinOp, bool>)((_source74) => {
        if (_source74.is_Eq) {
          bool _2058___mcc_h0 = _source74.dtor_referential;
          bool _2059___mcc_h1 = _source74.dtor_nullable;
          return false;
        } else if (_source74.is_Div) {
          return false;
        } else if (_source74.is_EuclidianDiv) {
          return false;
        } else if (_source74.is_Mod) {
          return false;
        } else if (_source74.is_EuclidianMod) {
          return false;
        } else if (_source74.is_Lt) {
          return false;
        } else if (_source74.is_LtChar) {
          return false;
        } else if (_source74.is_Plus) {
          return false;
        } else if (_source74.is_Minus) {
          return false;
        } else if (_source74.is_Times) {
          return false;
        } else if (_source74.is_BitwiseAnd) {
          return false;
        } else if (_source74.is_BitwiseOr) {
          return false;
        } else if (_source74.is_BitwiseXor) {
          return false;
        } else if (_source74.is_BitwiseShiftRight) {
          return false;
        } else if (_source74.is_BitwiseShiftLeft) {
          return false;
        } else if (_source74.is_And) {
          return false;
        } else if (_source74.is_Or) {
          return false;
        } else if (_source74.is_In) {
          return false;
        } else if (_source74.is_SeqProperPrefix) {
          return false;
        } else if (_source74.is_SeqPrefix) {
          return false;
        } else if (_source74.is_SetMerge) {
          return true;
        } else if (_source74.is_SetSubtraction) {
          return true;
        } else if (_source74.is_SetIntersection) {
          return true;
        } else if (_source74.is_Subset) {
          return false;
        } else if (_source74.is_ProperSubset) {
          return false;
        } else if (_source74.is_SetDisjoint) {
          return true;
        } else if (_source74.is_MapMerge) {
          return true;
        } else if (_source74.is_MapSubtraction) {
          return true;
        } else if (_source74.is_MultisetMerge) {
          return true;
        } else if (_source74.is_MultisetSubtraction) {
          return true;
        } else if (_source74.is_MultisetIntersection) {
          return true;
        } else if (_source74.is_Submultiset) {
          return false;
        } else if (_source74.is_ProperSubmultiset) {
          return false;
        } else if (_source74.is_MultisetDisjoint) {
          return true;
        } else if (_source74.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _2060___mcc_h4 = _source74.dtor_Passthrough_a0;
          return false;
        }
      }))(_2053_op);
      bool _2061_becomesRightCallsLeft;
      _2061_becomesRightCallsLeft = ((System.Func<DAST._IBinOp, bool>)((_source75) => {
        if (_source75.is_Eq) {
          bool _2062___mcc_h6 = _source75.dtor_referential;
          bool _2063___mcc_h7 = _source75.dtor_nullable;
          return false;
        } else if (_source75.is_Div) {
          return false;
        } else if (_source75.is_EuclidianDiv) {
          return false;
        } else if (_source75.is_Mod) {
          return false;
        } else if (_source75.is_EuclidianMod) {
          return false;
        } else if (_source75.is_Lt) {
          return false;
        } else if (_source75.is_LtChar) {
          return false;
        } else if (_source75.is_Plus) {
          return false;
        } else if (_source75.is_Minus) {
          return false;
        } else if (_source75.is_Times) {
          return false;
        } else if (_source75.is_BitwiseAnd) {
          return false;
        } else if (_source75.is_BitwiseOr) {
          return false;
        } else if (_source75.is_BitwiseXor) {
          return false;
        } else if (_source75.is_BitwiseShiftRight) {
          return false;
        } else if (_source75.is_BitwiseShiftLeft) {
          return false;
        } else if (_source75.is_And) {
          return false;
        } else if (_source75.is_Or) {
          return false;
        } else if (_source75.is_In) {
          return true;
        } else if (_source75.is_SeqProperPrefix) {
          return false;
        } else if (_source75.is_SeqPrefix) {
          return false;
        } else if (_source75.is_SetMerge) {
          return false;
        } else if (_source75.is_SetSubtraction) {
          return false;
        } else if (_source75.is_SetIntersection) {
          return false;
        } else if (_source75.is_Subset) {
          return false;
        } else if (_source75.is_ProperSubset) {
          return false;
        } else if (_source75.is_SetDisjoint) {
          return false;
        } else if (_source75.is_MapMerge) {
          return false;
        } else if (_source75.is_MapSubtraction) {
          return false;
        } else if (_source75.is_MultisetMerge) {
          return false;
        } else if (_source75.is_MultisetSubtraction) {
          return false;
        } else if (_source75.is_MultisetIntersection) {
          return false;
        } else if (_source75.is_Submultiset) {
          return false;
        } else if (_source75.is_ProperSubmultiset) {
          return false;
        } else if (_source75.is_MultisetDisjoint) {
          return false;
        } else if (_source75.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2064___mcc_h10 = _source75.dtor_Passthrough_a0;
          return false;
        }
      }))(_2053_op);
      bool _2065_becomesCallLeftRight;
      _2065_becomesCallLeftRight = ((System.Func<DAST._IBinOp, bool>)((_source76) => {
        if (_source76.is_Eq) {
          bool _2066___mcc_h12 = _source76.dtor_referential;
          bool _2067___mcc_h13 = _source76.dtor_nullable;
          if ((_2066___mcc_h12) == (true)) {
            if ((_2067___mcc_h13) == (false)) {
              return true;
            } else {
              return false;
            }
          } else {
            return false;
          }
        } else if (_source76.is_Div) {
          return false;
        } else if (_source76.is_EuclidianDiv) {
          return false;
        } else if (_source76.is_Mod) {
          return false;
        } else if (_source76.is_EuclidianMod) {
          return false;
        } else if (_source76.is_Lt) {
          return false;
        } else if (_source76.is_LtChar) {
          return false;
        } else if (_source76.is_Plus) {
          return false;
        } else if (_source76.is_Minus) {
          return false;
        } else if (_source76.is_Times) {
          return false;
        } else if (_source76.is_BitwiseAnd) {
          return false;
        } else if (_source76.is_BitwiseOr) {
          return false;
        } else if (_source76.is_BitwiseXor) {
          return false;
        } else if (_source76.is_BitwiseShiftRight) {
          return false;
        } else if (_source76.is_BitwiseShiftLeft) {
          return false;
        } else if (_source76.is_And) {
          return false;
        } else if (_source76.is_Or) {
          return false;
        } else if (_source76.is_In) {
          return false;
        } else if (_source76.is_SeqProperPrefix) {
          return false;
        } else if (_source76.is_SeqPrefix) {
          return false;
        } else if (_source76.is_SetMerge) {
          return false;
        } else if (_source76.is_SetSubtraction) {
          return false;
        } else if (_source76.is_SetIntersection) {
          return false;
        } else if (_source76.is_Subset) {
          return false;
        } else if (_source76.is_ProperSubset) {
          return false;
        } else if (_source76.is_SetDisjoint) {
          return false;
        } else if (_source76.is_MapMerge) {
          return false;
        } else if (_source76.is_MapSubtraction) {
          return false;
        } else if (_source76.is_MultisetMerge) {
          return false;
        } else if (_source76.is_MultisetSubtraction) {
          return false;
        } else if (_source76.is_MultisetIntersection) {
          return false;
        } else if (_source76.is_Submultiset) {
          return false;
        } else if (_source76.is_ProperSubmultiset) {
          return false;
        } else if (_source76.is_MultisetDisjoint) {
          return false;
        } else if (_source76.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2068___mcc_h16 = _source76.dtor_Passthrough_a0;
          return false;
        }
      }))(_2053_op);
      DCOMP._IOwnership _2069_expectedLeftOwnership;
      _2069_expectedLeftOwnership = ((_2057_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_2061_becomesRightCallsLeft) || (_2065_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _2070_expectedRightOwnership;
      _2070_expectedRightOwnership = (((_2057_becomesLeftCallsRight) || (_2065_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_2061_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _2071_left;
      DCOMP._IOwnership _2072___v54;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2073_recIdentsL;
      RAST._IExpr _out189;
      DCOMP._IOwnership _out190;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
      (this).GenExpr(_2054_lExpr, selfIdent, @params, _2069_expectedLeftOwnership, out _out189, out _out190, out _out191);
      _2071_left = _out189;
      _2072___v54 = _out190;
      _2073_recIdentsL = _out191;
      RAST._IExpr _2074_right;
      DCOMP._IOwnership _2075___v55;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2076_recIdentsR;
      RAST._IExpr _out192;
      DCOMP._IOwnership _out193;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
      (this).GenExpr(_2055_rExpr, selfIdent, @params, _2070_expectedRightOwnership, out _out192, out _out193, out _out194);
      _2074_right = _out192;
      _2075___v55 = _out193;
      _2076_recIdentsR = _out194;
      DAST._IBinOp _source77 = _2053_op;
      if (_source77.is_Eq) {
        bool _2077___mcc_h18 = _source77.dtor_referential;
        bool _2078___mcc_h19 = _source77.dtor_nullable;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source78 = _2053_op;
            if (_source78.is_Eq) {
              bool _2079___mcc_h24 = _source78.dtor_referential;
              bool _2080___mcc_h25 = _source78.dtor_nullable;
              bool _2081_nullable = _2080___mcc_h25;
              bool _2082_referential = _2079___mcc_h24;
              {
                if (_2082_referential) {
                  if (_2081_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source78.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source78.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2083___mcc_h26 = _source78.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2084_op = _2083___mcc_h26;
              {
                r = RAST.Expr.create_BinaryOp(_2084_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_Div) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source79 = _2053_op;
            if (_source79.is_Eq) {
              bool _2085___mcc_h27 = _source79.dtor_referential;
              bool _2086___mcc_h28 = _source79.dtor_nullable;
              bool _2087_nullable = _2086___mcc_h28;
              bool _2088_referential = _2085___mcc_h27;
              {
                if (_2088_referential) {
                  if (_2087_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source79.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source79.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2089___mcc_h29 = _source79.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2090_op = _2089___mcc_h29;
              {
                r = RAST.Expr.create_BinaryOp(_2090_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_EuclidianDiv) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source80 = _2053_op;
            if (_source80.is_Eq) {
              bool _2091___mcc_h30 = _source80.dtor_referential;
              bool _2092___mcc_h31 = _source80.dtor_nullable;
              bool _2093_nullable = _2092___mcc_h31;
              bool _2094_referential = _2091___mcc_h30;
              {
                if (_2094_referential) {
                  if (_2093_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source80.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source80.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2095___mcc_h32 = _source80.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2096_op = _2095___mcc_h32;
              {
                r = RAST.Expr.create_BinaryOp(_2096_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_Mod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source81 = _2053_op;
            if (_source81.is_Eq) {
              bool _2097___mcc_h33 = _source81.dtor_referential;
              bool _2098___mcc_h34 = _source81.dtor_nullable;
              bool _2099_nullable = _2098___mcc_h34;
              bool _2100_referential = _2097___mcc_h33;
              {
                if (_2100_referential) {
                  if (_2099_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source81.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source81.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2101___mcc_h35 = _source81.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2102_op = _2101___mcc_h35;
              {
                r = RAST.Expr.create_BinaryOp(_2102_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_EuclidianMod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source82 = _2053_op;
            if (_source82.is_Eq) {
              bool _2103___mcc_h36 = _source82.dtor_referential;
              bool _2104___mcc_h37 = _source82.dtor_nullable;
              bool _2105_nullable = _2104___mcc_h37;
              bool _2106_referential = _2103___mcc_h36;
              {
                if (_2106_referential) {
                  if (_2105_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source82.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source82.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2107___mcc_h38 = _source82.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2108_op = _2107___mcc_h38;
              {
                r = RAST.Expr.create_BinaryOp(_2108_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_Lt) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source83 = _2053_op;
            if (_source83.is_Eq) {
              bool _2109___mcc_h39 = _source83.dtor_referential;
              bool _2110___mcc_h40 = _source83.dtor_nullable;
              bool _2111_nullable = _2110___mcc_h40;
              bool _2112_referential = _2109___mcc_h39;
              {
                if (_2112_referential) {
                  if (_2111_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source83.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source83.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2113___mcc_h41 = _source83.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2114_op = _2113___mcc_h41;
              {
                r = RAST.Expr.create_BinaryOp(_2114_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_LtChar) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source84 = _2053_op;
            if (_source84.is_Eq) {
              bool _2115___mcc_h42 = _source84.dtor_referential;
              bool _2116___mcc_h43 = _source84.dtor_nullable;
              bool _2117_nullable = _2116___mcc_h43;
              bool _2118_referential = _2115___mcc_h42;
              {
                if (_2118_referential) {
                  if (_2117_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source84.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source84.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2119___mcc_h44 = _source84.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2120_op = _2119___mcc_h44;
              {
                r = RAST.Expr.create_BinaryOp(_2120_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_Plus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source85 = _2053_op;
            if (_source85.is_Eq) {
              bool _2121___mcc_h45 = _source85.dtor_referential;
              bool _2122___mcc_h46 = _source85.dtor_nullable;
              bool _2123_nullable = _2122___mcc_h46;
              bool _2124_referential = _2121___mcc_h45;
              {
                if (_2124_referential) {
                  if (_2123_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source85.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source85.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2125___mcc_h47 = _source85.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2126_op = _2125___mcc_h47;
              {
                r = RAST.Expr.create_BinaryOp(_2126_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_Minus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source86 = _2053_op;
            if (_source86.is_Eq) {
              bool _2127___mcc_h48 = _source86.dtor_referential;
              bool _2128___mcc_h49 = _source86.dtor_nullable;
              bool _2129_nullable = _2128___mcc_h49;
              bool _2130_referential = _2127___mcc_h48;
              {
                if (_2130_referential) {
                  if (_2129_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source86.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source86.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2131___mcc_h50 = _source86.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2132_op = _2131___mcc_h50;
              {
                r = RAST.Expr.create_BinaryOp(_2132_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_Times) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source87 = _2053_op;
            if (_source87.is_Eq) {
              bool _2133___mcc_h51 = _source87.dtor_referential;
              bool _2134___mcc_h52 = _source87.dtor_nullable;
              bool _2135_nullable = _2134___mcc_h52;
              bool _2136_referential = _2133___mcc_h51;
              {
                if (_2136_referential) {
                  if (_2135_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source87.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source87.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2137___mcc_h53 = _source87.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2138_op = _2137___mcc_h53;
              {
                r = RAST.Expr.create_BinaryOp(_2138_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_BitwiseAnd) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source88 = _2053_op;
            if (_source88.is_Eq) {
              bool _2139___mcc_h54 = _source88.dtor_referential;
              bool _2140___mcc_h55 = _source88.dtor_nullable;
              bool _2141_nullable = _2140___mcc_h55;
              bool _2142_referential = _2139___mcc_h54;
              {
                if (_2142_referential) {
                  if (_2141_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source88.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source88.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2143___mcc_h56 = _source88.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2144_op = _2143___mcc_h56;
              {
                r = RAST.Expr.create_BinaryOp(_2144_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_BitwiseOr) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source89 = _2053_op;
            if (_source89.is_Eq) {
              bool _2145___mcc_h57 = _source89.dtor_referential;
              bool _2146___mcc_h58 = _source89.dtor_nullable;
              bool _2147_nullable = _2146___mcc_h58;
              bool _2148_referential = _2145___mcc_h57;
              {
                if (_2148_referential) {
                  if (_2147_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source89.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source89.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2149___mcc_h59 = _source89.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2150_op = _2149___mcc_h59;
              {
                r = RAST.Expr.create_BinaryOp(_2150_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_BitwiseXor) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source90 = _2053_op;
            if (_source90.is_Eq) {
              bool _2151___mcc_h60 = _source90.dtor_referential;
              bool _2152___mcc_h61 = _source90.dtor_nullable;
              bool _2153_nullable = _2152___mcc_h61;
              bool _2154_referential = _2151___mcc_h60;
              {
                if (_2154_referential) {
                  if (_2153_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source90.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source90.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2155___mcc_h62 = _source90.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2156_op = _2155___mcc_h62;
              {
                r = RAST.Expr.create_BinaryOp(_2156_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_BitwiseShiftRight) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source91 = _2053_op;
            if (_source91.is_Eq) {
              bool _2157___mcc_h63 = _source91.dtor_referential;
              bool _2158___mcc_h64 = _source91.dtor_nullable;
              bool _2159_nullable = _2158___mcc_h64;
              bool _2160_referential = _2157___mcc_h63;
              {
                if (_2160_referential) {
                  if (_2159_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source91.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source91.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2161___mcc_h65 = _source91.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2162_op = _2161___mcc_h65;
              {
                r = RAST.Expr.create_BinaryOp(_2162_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_BitwiseShiftLeft) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source92 = _2053_op;
            if (_source92.is_Eq) {
              bool _2163___mcc_h66 = _source92.dtor_referential;
              bool _2164___mcc_h67 = _source92.dtor_nullable;
              bool _2165_nullable = _2164___mcc_h67;
              bool _2166_referential = _2163___mcc_h66;
              {
                if (_2166_referential) {
                  if (_2165_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source92.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source92.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2167___mcc_h68 = _source92.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2168_op = _2167___mcc_h68;
              {
                r = RAST.Expr.create_BinaryOp(_2168_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_And) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source93 = _2053_op;
            if (_source93.is_Eq) {
              bool _2169___mcc_h69 = _source93.dtor_referential;
              bool _2170___mcc_h70 = _source93.dtor_nullable;
              bool _2171_nullable = _2170___mcc_h70;
              bool _2172_referential = _2169___mcc_h69;
              {
                if (_2172_referential) {
                  if (_2171_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source93.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source93.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2173___mcc_h71 = _source93.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2174_op = _2173___mcc_h71;
              {
                r = RAST.Expr.create_BinaryOp(_2174_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_Or) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source94 = _2053_op;
            if (_source94.is_Eq) {
              bool _2175___mcc_h72 = _source94.dtor_referential;
              bool _2176___mcc_h73 = _source94.dtor_nullable;
              bool _2177_nullable = _2176___mcc_h73;
              bool _2178_referential = _2175___mcc_h72;
              {
                if (_2178_referential) {
                  if (_2177_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source94.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source94.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2179___mcc_h74 = _source94.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2180_op = _2179___mcc_h74;
              {
                r = RAST.Expr.create_BinaryOp(_2180_op, _2071_left, _2074_right, _2056_format);
              }
            }
          }
        }
      } else if (_source77.is_In) {
        {
          r = ((_2074_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_2071_left);
        }
      } else if (_source77.is_SeqProperPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2071_left, _2074_right, _2056_format);
      } else if (_source77.is_SeqPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2071_left, _2074_right, _2056_format);
      } else if (_source77.is_SetMerge) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2074_right);
        }
      } else if (_source77.is_SetSubtraction) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2074_right);
        }
      } else if (_source77.is_SetIntersection) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2074_right);
        }
      } else if (_source77.is_Subset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2071_left, _2074_right, _2056_format);
        }
      } else if (_source77.is_ProperSubset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2071_left, _2074_right, _2056_format);
        }
      } else if (_source77.is_SetDisjoint) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2074_right);
        }
      } else if (_source77.is_MapMerge) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2074_right);
        }
      } else if (_source77.is_MapSubtraction) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2074_right);
        }
      } else if (_source77.is_MultisetMerge) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2074_right);
        }
      } else if (_source77.is_MultisetSubtraction) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2074_right);
        }
      } else if (_source77.is_MultisetIntersection) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2074_right);
        }
      } else if (_source77.is_Submultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2071_left, _2074_right, _2056_format);
        }
      } else if (_source77.is_ProperSubmultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2071_left, _2074_right, _2056_format);
        }
      } else if (_source77.is_MultisetDisjoint) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2074_right);
        }
      } else if (_source77.is_Concat) {
        {
          r = ((_2071_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_2074_right);
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _2181___mcc_h22 = _source77.dtor_Passthrough_a0;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2053_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2053_op), _2071_left, _2074_right, _2056_format);
          } else {
            DAST._IBinOp _source95 = _2053_op;
            if (_source95.is_Eq) {
              bool _2182___mcc_h75 = _source95.dtor_referential;
              bool _2183___mcc_h76 = _source95.dtor_nullable;
              bool _2184_nullable = _2183___mcc_h76;
              bool _2185_referential = _2182___mcc_h75;
              {
                if (_2185_referential) {
                  if (_2184_nullable) {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  } else {
                    r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2071_left, _2074_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source95.is_EuclidianDiv) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else if (_source95.is_EuclidianMod) {
              {
                r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_2071_left, _2074_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2186___mcc_h77 = _source95.dtor_Passthrough_a0;
              Dafny.ISequence<Dafny.Rune> _2187_op = _2186___mcc_h77;
              {
                r = RAST.Expr.create_BinaryOp(_2187_op, _2071_left, _2074_right, _2056_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2073_recIdentsL, _2076_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs50 = e;
      DAST._IExpression _2188_expr = _let_tmp_rhs50.dtor_value;
      DAST._IType _2189_fromTpe = _let_tmp_rhs50.dtor_from;
      DAST._IType _2190_toTpe = _let_tmp_rhs50.dtor_typ;
      RAST._IExpr _2191_recursiveGen;
      DCOMP._IOwnership _2192_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2193_recIdents;
      RAST._IExpr _out197;
      DCOMP._IOwnership _out198;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out199;
      (this).GenExpr(_2188_expr, selfIdent, @params, expectedOwnership, out _out197, out _out198, out _out199);
      _2191_recursiveGen = _out197;
      _2192_recOwned = _out198;
      _2193_recIdents = _out199;
      r = _2191_recursiveGen;
      if (object.Equals(_2192_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out200;
      DCOMP._IOwnership _out201;
      DCOMP.COMP.FromOwnership(r, _2192_recOwned, expectedOwnership, out _out200, out _out201);
      r = _out200;
      resultingOwnership = _out201;
      readIdents = _2193_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs51 = e;
      DAST._IExpression _2194_expr = _let_tmp_rhs51.dtor_value;
      DAST._IType _2195_fromTpe = _let_tmp_rhs51.dtor_from;
      DAST._IType _2196_toTpe = _let_tmp_rhs51.dtor_typ;
      RAST._IExpr _2197_recursiveGen;
      DCOMP._IOwnership _2198_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2199_recIdents;
      RAST._IExpr _out202;
      DCOMP._IOwnership _out203;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
      (this).GenExpr(_2194_expr, selfIdent, @params, expectedOwnership, out _out202, out _out203, out _out204);
      _2197_recursiveGen = _out202;
      _2198_recOwned = _out203;
      _2199_recIdents = _out204;
      r = _2197_recursiveGen;
      if (object.Equals(_2198_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out205;
      DCOMP._IOwnership _out206;
      DCOMP.COMP.FromOwnership(r, _2198_recOwned, expectedOwnership, out _out205, out _out206);
      r = _out205;
      resultingOwnership = _out206;
      readIdents = _2199_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs52 = e;
      DAST._IExpression _2200_expr = _let_tmp_rhs52.dtor_value;
      DAST._IType _2201_fromTpe = _let_tmp_rhs52.dtor_from;
      DAST._IType _2202_toTpe = _let_tmp_rhs52.dtor_typ;
      DAST._IType _let_tmp_rhs53 = _2202_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2203___v57 = _let_tmp_rhs53.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _2204___v58 = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs54 = _let_tmp_rhs53.dtor_resolved;
      DAST._IType _2205_b = _let_tmp_rhs54.dtor_baseType;
      DAST._INewtypeRange _2206_range = _let_tmp_rhs54.dtor_range;
      bool _2207_erase = _let_tmp_rhs54.dtor_erase;
      if (object.Equals(_2201_fromTpe, _2205_b)) {
        RAST._IExpr _2208_recursiveGen;
        DCOMP._IOwnership _2209_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2210_recIdents;
        RAST._IExpr _out207;
        DCOMP._IOwnership _out208;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
        (this).GenExpr(_2200_expr, selfIdent, @params, expectedOwnership, out _out207, out _out208, out _out209);
        _2208_recursiveGen = _out207;
        _2209_recOwned = _out208;
        _2210_recIdents = _out209;
        Std.Wrappers._IOption<RAST._IType> _2211_potentialRhsType;
        _2211_potentialRhsType = DCOMP.COMP.NewtypeToRustType(_2205_b, _2206_range);
        Std.Wrappers._IOption<RAST._IType> _source96 = _2211_potentialRhsType;
        if (_source96.is_None) {
          if (_2207_erase) {
            r = _2208_recursiveGen;
          } else {
            RAST._IType _2212_rhsType;
            RAST._IType _out210;
            _out210 = (this).GenType(_2202_toTpe, true, false);
            _2212_rhsType = _out210;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_2212_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_2208_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out211;
          DCOMP._IOwnership _out212;
          DCOMP.COMP.FromOwnership(r, _2209_recOwned, expectedOwnership, out _out211, out _out212);
          r = _out211;
          resultingOwnership = _out212;
        } else {
          RAST._IType _2213___mcc_h0 = _source96.dtor_value;
          RAST._IType _2214_v = _2213___mcc_h0;
          r = RAST.Expr.create_ConversionNum(_2214_v, _2208_recursiveGen);
          RAST._IExpr _out213;
          DCOMP._IOwnership _out214;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out213, out _out214);
          r = _out213;
          resultingOwnership = _out214;
        }
        readIdents = _2210_recIdents;
      } else {
        RAST._IExpr _out215;
        DCOMP._IOwnership _out216;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out217;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_2200_expr, _2201_fromTpe, _2205_b), _2205_b, _2202_toTpe), selfIdent, @params, expectedOwnership, out _out215, out _out216, out _out217);
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
      DAST._IExpression _2215_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _2216_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _2217_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _2216_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2218___v59 = _let_tmp_rhs56.dtor_Path_a0;
      Dafny.ISequence<DAST._IType> _2219___v60 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _2220_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _2221_range = _let_tmp_rhs57.dtor_range;
      bool _2222_erase = _let_tmp_rhs57.dtor_erase;
      if (object.Equals(_2220_b, _2217_toTpe)) {
        RAST._IExpr _2223_recursiveGen;
        DCOMP._IOwnership _2224_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2225_recIdents;
        RAST._IExpr _out218;
        DCOMP._IOwnership _out219;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out220;
        (this).GenExpr(_2215_expr, selfIdent, @params, expectedOwnership, out _out218, out _out219, out _out220);
        _2223_recursiveGen = _out218;
        _2224_recOwned = _out219;
        _2225_recIdents = _out220;
        if (_2222_erase) {
          r = _2223_recursiveGen;
        } else {
          r = (_2223_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
        }
        RAST._IExpr _out221;
        DCOMP._IOwnership _out222;
        DCOMP.COMP.FromOwnership(r, _2224_recOwned, expectedOwnership, out _out221, out _out222);
        r = _out221;
        resultingOwnership = _out222;
        readIdents = _2225_recIdents;
      } else {
        RAST._IExpr _out223;
        DCOMP._IOwnership _out224;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_2215_expr, _2216_fromTpe, _2220_b), _2220_b, _2217_toTpe), selfIdent, @params, expectedOwnership, out _out223, out _out224, out _out225);
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
      DAST._IExpression _2226_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _2227_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _2228_toTpe = _let_tmp_rhs58.dtor_typ;
      RAST._IExpr _2229_recursiveGen;
      DCOMP._IOwnership _2230_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2231_recIdents;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_2226_expr, selfIdent, @params, expectedOwnership, out _out226, out _out227, out _out228);
      _2229_recursiveGen = _out226;
      _2230_recOwned = _out227;
      _2231_recIdents = _out228;
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_2229_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)")));
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out229, out _out230);
      r = _out229;
      resultingOwnership = _out230;
      readIdents = _2231_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs59 = e;
      DAST._IExpression _2232_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _2233_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _2234_toTpe = _let_tmp_rhs59.dtor_typ;
      if (object.Equals(_2233_fromTpe, _2234_toTpe)) {
        RAST._IExpr _2235_recursiveGen;
        DCOMP._IOwnership _2236_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2237_recIdents;
        RAST._IExpr _out231;
        DCOMP._IOwnership _out232;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out233;
        (this).GenExpr(_2232_expr, selfIdent, @params, expectedOwnership, out _out231, out _out232, out _out233);
        _2235_recursiveGen = _out231;
        _2236_recOwned = _out232;
        _2237_recIdents = _out233;
        r = _2235_recursiveGen;
        RAST._IExpr _out234;
        DCOMP._IOwnership _out235;
        DCOMP.COMP.FromOwnership(r, _2236_recOwned, expectedOwnership, out _out234, out _out235);
        r = _out234;
        resultingOwnership = _out235;
        readIdents = _2237_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source97 = _System.Tuple2<DAST._IType, DAST._IType>.create(_2233_fromTpe, _2234_toTpe);
        DAST._IType _2238___mcc_h0 = _source97.dtor__0;
        DAST._IType _2239___mcc_h1 = _source97.dtor__1;
        DAST._IType _source98 = _2238___mcc_h0;
        if (_source98.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2240___mcc_h4 = _source98.dtor_Path_a0;
          Dafny.ISequence<DAST._IType> _2241___mcc_h5 = _source98.dtor_typeArgs;
          DAST._IResolvedType _2242___mcc_h6 = _source98.dtor_resolved;
          DAST._IResolvedType _source99 = _2242___mcc_h6;
          if (_source99.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2243___mcc_h16 = _source99.dtor_path;
            DAST._IType _source100 = _2239___mcc_h1;
            if (_source100.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2244___mcc_h20 = _source100.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2245___mcc_h21 = _source100.dtor_typeArgs;
              DAST._IResolvedType _2246___mcc_h22 = _source100.dtor_resolved;
              DAST._IResolvedType _source101 = _2246___mcc_h22;
              if (_source101.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2247___mcc_h26 = _source101.dtor_path;
                {
                  RAST._IExpr _out236;
                  DCOMP._IOwnership _out237;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out238;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out236, out _out237, out _out238);
                  r = _out236;
                  resultingOwnership = _out237;
                  readIdents = _out238;
                }
              } else if (_source101.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2248___mcc_h28 = _source101.dtor_path;
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
                DAST._IType _2249___mcc_h30 = _source101.dtor_baseType;
                DAST._INewtypeRange _2250___mcc_h31 = _source101.dtor_range;
                bool _2251___mcc_h32 = _source101.dtor_erase;
                bool _2252_erase = _2251___mcc_h32;
                DAST._INewtypeRange _2253_range = _2250___mcc_h31;
                DAST._IType _2254_b = _2249___mcc_h30;
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
            } else if (_source100.is_Nullable) {
              DAST._IType _2255___mcc_h36 = _source100.dtor_Nullable_a0;
              {
                RAST._IExpr _out245;
                DCOMP._IOwnership _out246;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out247;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out245, out _out246, out _out247);
                r = _out245;
                resultingOwnership = _out246;
                readIdents = _out247;
              }
            } else if (_source100.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2256___mcc_h38 = _source100.dtor_Tuple_a0;
              {
                RAST._IExpr _out248;
                DCOMP._IOwnership _out249;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out248, out _out249, out _out250);
                r = _out248;
                resultingOwnership = _out249;
                readIdents = _out250;
              }
            } else if (_source100.is_Array) {
              DAST._IType _2257___mcc_h40 = _source100.dtor_element;
              BigInteger _2258___mcc_h41 = _source100.dtor_dims;
              {
                RAST._IExpr _out251;
                DCOMP._IOwnership _out252;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out251, out _out252, out _out253);
                r = _out251;
                resultingOwnership = _out252;
                readIdents = _out253;
              }
            } else if (_source100.is_Seq) {
              DAST._IType _2259___mcc_h44 = _source100.dtor_element;
              {
                RAST._IExpr _out254;
                DCOMP._IOwnership _out255;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out256;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out254, out _out255, out _out256);
                r = _out254;
                resultingOwnership = _out255;
                readIdents = _out256;
              }
            } else if (_source100.is_Set) {
              DAST._IType _2260___mcc_h46 = _source100.dtor_element;
              {
                RAST._IExpr _out257;
                DCOMP._IOwnership _out258;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out259;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out257, out _out258, out _out259);
                r = _out257;
                resultingOwnership = _out258;
                readIdents = _out259;
              }
            } else if (_source100.is_Multiset) {
              DAST._IType _2261___mcc_h48 = _source100.dtor_element;
              {
                RAST._IExpr _out260;
                DCOMP._IOwnership _out261;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out260, out _out261, out _out262);
                r = _out260;
                resultingOwnership = _out261;
                readIdents = _out262;
              }
            } else if (_source100.is_Map) {
              DAST._IType _2262___mcc_h50 = _source100.dtor_key;
              DAST._IType _2263___mcc_h51 = _source100.dtor_value;
              {
                RAST._IExpr _out263;
                DCOMP._IOwnership _out264;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out263, out _out264, out _out265);
                r = _out263;
                resultingOwnership = _out264;
                readIdents = _out265;
              }
            } else if (_source100.is_SetBuilder) {
              DAST._IType _2264___mcc_h54 = _source100.dtor_element;
              {
                RAST._IExpr _out266;
                DCOMP._IOwnership _out267;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out268;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out266, out _out267, out _out268);
                r = _out266;
                resultingOwnership = _out267;
                readIdents = _out268;
              }
            } else if (_source100.is_MapBuilder) {
              DAST._IType _2265___mcc_h56 = _source100.dtor_key;
              DAST._IType _2266___mcc_h57 = _source100.dtor_value;
              {
                RAST._IExpr _out269;
                DCOMP._IOwnership _out270;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out269, out _out270, out _out271);
                r = _out269;
                resultingOwnership = _out270;
                readIdents = _out271;
              }
            } else if (_source100.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2267___mcc_h60 = _source100.dtor_args;
              DAST._IType _2268___mcc_h61 = _source100.dtor_result;
              {
                RAST._IExpr _out272;
                DCOMP._IOwnership _out273;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out272, out _out273, out _out274);
                r = _out272;
                resultingOwnership = _out273;
                readIdents = _out274;
              }
            } else if (_source100.is_Primitive) {
              DAST._IPrimitive _2269___mcc_h64 = _source100.dtor_Primitive_a0;
              {
                RAST._IExpr _out275;
                DCOMP._IOwnership _out276;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out275, out _out276, out _out277);
                r = _out275;
                resultingOwnership = _out276;
                readIdents = _out277;
              }
            } else if (_source100.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2270___mcc_h66 = _source100.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _2271___mcc_h68 = _source100.dtor_TypeArg_a0;
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
          } else if (_source99.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2272___mcc_h70 = _source99.dtor_path;
            DAST._IType _source102 = _2239___mcc_h1;
            if (_source102.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2273___mcc_h74 = _source102.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2274___mcc_h75 = _source102.dtor_typeArgs;
              DAST._IResolvedType _2275___mcc_h76 = _source102.dtor_resolved;
              DAST._IResolvedType _source103 = _2275___mcc_h76;
              if (_source103.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2276___mcc_h80 = _source103.dtor_path;
                {
                  RAST._IExpr _out284;
                  DCOMP._IOwnership _out285;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out284, out _out285, out _out286);
                  r = _out284;
                  resultingOwnership = _out285;
                  readIdents = _out286;
                }
              } else if (_source103.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2277___mcc_h82 = _source103.dtor_path;
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
                DAST._IType _2278___mcc_h84 = _source103.dtor_baseType;
                DAST._INewtypeRange _2279___mcc_h85 = _source103.dtor_range;
                bool _2280___mcc_h86 = _source103.dtor_erase;
                bool _2281_erase = _2280___mcc_h86;
                DAST._INewtypeRange _2282_range = _2279___mcc_h85;
                DAST._IType _2283_b = _2278___mcc_h84;
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
            } else if (_source102.is_Nullable) {
              DAST._IType _2284___mcc_h90 = _source102.dtor_Nullable_a0;
              {
                RAST._IExpr _out293;
                DCOMP._IOwnership _out294;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out295;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out293, out _out294, out _out295);
                r = _out293;
                resultingOwnership = _out294;
                readIdents = _out295;
              }
            } else if (_source102.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2285___mcc_h92 = _source102.dtor_Tuple_a0;
              {
                RAST._IExpr _out296;
                DCOMP._IOwnership _out297;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out296, out _out297, out _out298);
                r = _out296;
                resultingOwnership = _out297;
                readIdents = _out298;
              }
            } else if (_source102.is_Array) {
              DAST._IType _2286___mcc_h94 = _source102.dtor_element;
              BigInteger _2287___mcc_h95 = _source102.dtor_dims;
              {
                RAST._IExpr _out299;
                DCOMP._IOwnership _out300;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out299, out _out300, out _out301);
                r = _out299;
                resultingOwnership = _out300;
                readIdents = _out301;
              }
            } else if (_source102.is_Seq) {
              DAST._IType _2288___mcc_h98 = _source102.dtor_element;
              {
                RAST._IExpr _out302;
                DCOMP._IOwnership _out303;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out302, out _out303, out _out304);
                r = _out302;
                resultingOwnership = _out303;
                readIdents = _out304;
              }
            } else if (_source102.is_Set) {
              DAST._IType _2289___mcc_h100 = _source102.dtor_element;
              {
                RAST._IExpr _out305;
                DCOMP._IOwnership _out306;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out305, out _out306, out _out307);
                r = _out305;
                resultingOwnership = _out306;
                readIdents = _out307;
              }
            } else if (_source102.is_Multiset) {
              DAST._IType _2290___mcc_h102 = _source102.dtor_element;
              {
                RAST._IExpr _out308;
                DCOMP._IOwnership _out309;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out310;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out308, out _out309, out _out310);
                r = _out308;
                resultingOwnership = _out309;
                readIdents = _out310;
              }
            } else if (_source102.is_Map) {
              DAST._IType _2291___mcc_h104 = _source102.dtor_key;
              DAST._IType _2292___mcc_h105 = _source102.dtor_value;
              {
                RAST._IExpr _out311;
                DCOMP._IOwnership _out312;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out313;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out311, out _out312, out _out313);
                r = _out311;
                resultingOwnership = _out312;
                readIdents = _out313;
              }
            } else if (_source102.is_SetBuilder) {
              DAST._IType _2293___mcc_h108 = _source102.dtor_element;
              {
                RAST._IExpr _out314;
                DCOMP._IOwnership _out315;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out314, out _out315, out _out316);
                r = _out314;
                resultingOwnership = _out315;
                readIdents = _out316;
              }
            } else if (_source102.is_MapBuilder) {
              DAST._IType _2294___mcc_h110 = _source102.dtor_key;
              DAST._IType _2295___mcc_h111 = _source102.dtor_value;
              {
                RAST._IExpr _out317;
                DCOMP._IOwnership _out318;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out317, out _out318, out _out319);
                r = _out317;
                resultingOwnership = _out318;
                readIdents = _out319;
              }
            } else if (_source102.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2296___mcc_h114 = _source102.dtor_args;
              DAST._IType _2297___mcc_h115 = _source102.dtor_result;
              {
                RAST._IExpr _out320;
                DCOMP._IOwnership _out321;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out320, out _out321, out _out322);
                r = _out320;
                resultingOwnership = _out321;
                readIdents = _out322;
              }
            } else if (_source102.is_Primitive) {
              DAST._IPrimitive _2298___mcc_h118 = _source102.dtor_Primitive_a0;
              {
                RAST._IExpr _out323;
                DCOMP._IOwnership _out324;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out325;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out323, out _out324, out _out325);
                r = _out323;
                resultingOwnership = _out324;
                readIdents = _out325;
              }
            } else if (_source102.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2299___mcc_h120 = _source102.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _2300___mcc_h122 = _source102.dtor_TypeArg_a0;
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
            DAST._IType _2301___mcc_h124 = _source99.dtor_baseType;
            DAST._INewtypeRange _2302___mcc_h125 = _source99.dtor_range;
            bool _2303___mcc_h126 = _source99.dtor_erase;
            DAST._IType _source104 = _2239___mcc_h1;
            if (_source104.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2304___mcc_h136 = _source104.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2305___mcc_h137 = _source104.dtor_typeArgs;
              DAST._IResolvedType _2306___mcc_h138 = _source104.dtor_resolved;
              DAST._IResolvedType _source105 = _2306___mcc_h138;
              if (_source105.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2307___mcc_h145 = _source105.dtor_path;
                bool _2308_erase = _2303___mcc_h126;
                DAST._INewtypeRange _2309_range = _2302___mcc_h125;
                DAST._IType _2310_b = _2301___mcc_h124;
                {
                  RAST._IExpr _out332;
                  DCOMP._IOwnership _out333;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                  (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out332, out _out333, out _out334);
                  r = _out332;
                  resultingOwnership = _out333;
                  readIdents = _out334;
                }
              } else if (_source105.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2311___mcc_h148 = _source105.dtor_path;
                bool _2312_erase = _2303___mcc_h126;
                DAST._INewtypeRange _2313_range = _2302___mcc_h125;
                DAST._IType _2314_b = _2301___mcc_h124;
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
                DAST._IType _2315___mcc_h151 = _source105.dtor_baseType;
                DAST._INewtypeRange _2316___mcc_h152 = _source105.dtor_range;
                bool _2317___mcc_h153 = _source105.dtor_erase;
                bool _2318_erase = _2317___mcc_h153;
                DAST._INewtypeRange _2319_range = _2316___mcc_h152;
                DAST._IType _2320_b = _2315___mcc_h151;
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
            } else if (_source104.is_Nullable) {
              DAST._IType _2321___mcc_h160 = _source104.dtor_Nullable_a0;
              {
                RAST._IExpr _out341;
                DCOMP._IOwnership _out342;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out341, out _out342, out _out343);
                r = _out341;
                resultingOwnership = _out342;
                readIdents = _out343;
              }
            } else if (_source104.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2322___mcc_h163 = _source104.dtor_Tuple_a0;
              bool _2323_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2324_range = _2302___mcc_h125;
              DAST._IType _2325_b = _2301___mcc_h124;
              {
                RAST._IExpr _out344;
                DCOMP._IOwnership _out345;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out346;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out344, out _out345, out _out346);
                r = _out344;
                resultingOwnership = _out345;
                readIdents = _out346;
              }
            } else if (_source104.is_Array) {
              DAST._IType _2326___mcc_h166 = _source104.dtor_element;
              BigInteger _2327___mcc_h167 = _source104.dtor_dims;
              bool _2328_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2329_range = _2302___mcc_h125;
              DAST._IType _2330_b = _2301___mcc_h124;
              {
                RAST._IExpr _out347;
                DCOMP._IOwnership _out348;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out347, out _out348, out _out349);
                r = _out347;
                resultingOwnership = _out348;
                readIdents = _out349;
              }
            } else if (_source104.is_Seq) {
              DAST._IType _2331___mcc_h172 = _source104.dtor_element;
              bool _2332_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2333_range = _2302___mcc_h125;
              DAST._IType _2334_b = _2301___mcc_h124;
              {
                RAST._IExpr _out350;
                DCOMP._IOwnership _out351;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out350, out _out351, out _out352);
                r = _out350;
                resultingOwnership = _out351;
                readIdents = _out352;
              }
            } else if (_source104.is_Set) {
              DAST._IType _2335___mcc_h175 = _source104.dtor_element;
              bool _2336_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2337_range = _2302___mcc_h125;
              DAST._IType _2338_b = _2301___mcc_h124;
              {
                RAST._IExpr _out353;
                DCOMP._IOwnership _out354;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out353, out _out354, out _out355);
                r = _out353;
                resultingOwnership = _out354;
                readIdents = _out355;
              }
            } else if (_source104.is_Multiset) {
              DAST._IType _2339___mcc_h178 = _source104.dtor_element;
              bool _2340_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2341_range = _2302___mcc_h125;
              DAST._IType _2342_b = _2301___mcc_h124;
              {
                RAST._IExpr _out356;
                DCOMP._IOwnership _out357;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out356, out _out357, out _out358);
                r = _out356;
                resultingOwnership = _out357;
                readIdents = _out358;
              }
            } else if (_source104.is_Map) {
              DAST._IType _2343___mcc_h181 = _source104.dtor_key;
              DAST._IType _2344___mcc_h182 = _source104.dtor_value;
              bool _2345_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2346_range = _2302___mcc_h125;
              DAST._IType _2347_b = _2301___mcc_h124;
              {
                RAST._IExpr _out359;
                DCOMP._IOwnership _out360;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out359, out _out360, out _out361);
                r = _out359;
                resultingOwnership = _out360;
                readIdents = _out361;
              }
            } else if (_source104.is_SetBuilder) {
              DAST._IType _2348___mcc_h187 = _source104.dtor_element;
              bool _2349_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2350_range = _2302___mcc_h125;
              DAST._IType _2351_b = _2301___mcc_h124;
              {
                RAST._IExpr _out362;
                DCOMP._IOwnership _out363;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out362, out _out363, out _out364);
                r = _out362;
                resultingOwnership = _out363;
                readIdents = _out364;
              }
            } else if (_source104.is_MapBuilder) {
              DAST._IType _2352___mcc_h190 = _source104.dtor_key;
              DAST._IType _2353___mcc_h191 = _source104.dtor_value;
              bool _2354_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2355_range = _2302___mcc_h125;
              DAST._IType _2356_b = _2301___mcc_h124;
              {
                RAST._IExpr _out365;
                DCOMP._IOwnership _out366;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out365, out _out366, out _out367);
                r = _out365;
                resultingOwnership = _out366;
                readIdents = _out367;
              }
            } else if (_source104.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2357___mcc_h196 = _source104.dtor_args;
              DAST._IType _2358___mcc_h197 = _source104.dtor_result;
              bool _2359_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2360_range = _2302___mcc_h125;
              DAST._IType _2361_b = _2301___mcc_h124;
              {
                RAST._IExpr _out368;
                DCOMP._IOwnership _out369;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out370;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out368, out _out369, out _out370);
                r = _out368;
                resultingOwnership = _out369;
                readIdents = _out370;
              }
            } else if (_source104.is_Primitive) {
              DAST._IPrimitive _2362___mcc_h202 = _source104.dtor_Primitive_a0;
              bool _2363_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2364_range = _2302___mcc_h125;
              DAST._IType _2365_b = _2301___mcc_h124;
              {
                RAST._IExpr _out371;
                DCOMP._IOwnership _out372;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out371, out _out372, out _out373);
                r = _out371;
                resultingOwnership = _out372;
                readIdents = _out373;
              }
            } else if (_source104.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2366___mcc_h205 = _source104.dtor_Passthrough_a0;
              bool _2367_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2368_range = _2302___mcc_h125;
              DAST._IType _2369_b = _2301___mcc_h124;
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
              Dafny.ISequence<Dafny.Rune> _2370___mcc_h208 = _source104.dtor_TypeArg_a0;
              bool _2371_erase = _2303___mcc_h126;
              DAST._INewtypeRange _2372_range = _2302___mcc_h125;
              DAST._IType _2373_b = _2301___mcc_h124;
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
        } else if (_source98.is_Nullable) {
          DAST._IType _2374___mcc_h211 = _source98.dtor_Nullable_a0;
          DAST._IType _source106 = _2239___mcc_h1;
          if (_source106.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2375___mcc_h215 = _source106.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2376___mcc_h216 = _source106.dtor_typeArgs;
            DAST._IResolvedType _2377___mcc_h217 = _source106.dtor_resolved;
            DAST._IResolvedType _source107 = _2377___mcc_h217;
            if (_source107.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2378___mcc_h224 = _source107.dtor_path;
              {
                RAST._IExpr _out380;
                DCOMP._IOwnership _out381;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
                (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out380, out _out381, out _out382);
                r = _out380;
                resultingOwnership = _out381;
                readIdents = _out382;
              }
            } else if (_source107.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2379___mcc_h227 = _source107.dtor_path;
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
              DAST._IType _2380___mcc_h230 = _source107.dtor_baseType;
              DAST._INewtypeRange _2381___mcc_h231 = _source107.dtor_range;
              bool _2382___mcc_h232 = _source107.dtor_erase;
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
          } else if (_source106.is_Nullable) {
            DAST._IType _2383___mcc_h239 = _source106.dtor_Nullable_a0;
            {
              RAST._IExpr _out389;
              DCOMP._IOwnership _out390;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out389, out _out390, out _out391);
              r = _out389;
              resultingOwnership = _out390;
              readIdents = _out391;
            }
          } else if (_source106.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2384___mcc_h242 = _source106.dtor_Tuple_a0;
            {
              RAST._IExpr _out392;
              DCOMP._IOwnership _out393;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out394;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out392, out _out393, out _out394);
              r = _out392;
              resultingOwnership = _out393;
              readIdents = _out394;
            }
          } else if (_source106.is_Array) {
            DAST._IType _2385___mcc_h245 = _source106.dtor_element;
            BigInteger _2386___mcc_h246 = _source106.dtor_dims;
            {
              RAST._IExpr _out395;
              DCOMP._IOwnership _out396;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out397;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out395, out _out396, out _out397);
              r = _out395;
              resultingOwnership = _out396;
              readIdents = _out397;
            }
          } else if (_source106.is_Seq) {
            DAST._IType _2387___mcc_h251 = _source106.dtor_element;
            {
              RAST._IExpr _out398;
              DCOMP._IOwnership _out399;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out398, out _out399, out _out400);
              r = _out398;
              resultingOwnership = _out399;
              readIdents = _out400;
            }
          } else if (_source106.is_Set) {
            DAST._IType _2388___mcc_h254 = _source106.dtor_element;
            {
              RAST._IExpr _out401;
              DCOMP._IOwnership _out402;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out401, out _out402, out _out403);
              r = _out401;
              resultingOwnership = _out402;
              readIdents = _out403;
            }
          } else if (_source106.is_Multiset) {
            DAST._IType _2389___mcc_h257 = _source106.dtor_element;
            {
              RAST._IExpr _out404;
              DCOMP._IOwnership _out405;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out404, out _out405, out _out406);
              r = _out404;
              resultingOwnership = _out405;
              readIdents = _out406;
            }
          } else if (_source106.is_Map) {
            DAST._IType _2390___mcc_h260 = _source106.dtor_key;
            DAST._IType _2391___mcc_h261 = _source106.dtor_value;
            {
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out407, out _out408, out _out409);
              r = _out407;
              resultingOwnership = _out408;
              readIdents = _out409;
            }
          } else if (_source106.is_SetBuilder) {
            DAST._IType _2392___mcc_h266 = _source106.dtor_element;
            {
              RAST._IExpr _out410;
              DCOMP._IOwnership _out411;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out410, out _out411, out _out412);
              r = _out410;
              resultingOwnership = _out411;
              readIdents = _out412;
            }
          } else if (_source106.is_MapBuilder) {
            DAST._IType _2393___mcc_h269 = _source106.dtor_key;
            DAST._IType _2394___mcc_h270 = _source106.dtor_value;
            {
              RAST._IExpr _out413;
              DCOMP._IOwnership _out414;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out413, out _out414, out _out415);
              r = _out413;
              resultingOwnership = _out414;
              readIdents = _out415;
            }
          } else if (_source106.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2395___mcc_h275 = _source106.dtor_args;
            DAST._IType _2396___mcc_h276 = _source106.dtor_result;
            {
              RAST._IExpr _out416;
              DCOMP._IOwnership _out417;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out418;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out416, out _out417, out _out418);
              r = _out416;
              resultingOwnership = _out417;
              readIdents = _out418;
            }
          } else if (_source106.is_Primitive) {
            DAST._IPrimitive _2397___mcc_h281 = _source106.dtor_Primitive_a0;
            {
              RAST._IExpr _out419;
              DCOMP._IOwnership _out420;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out419, out _out420, out _out421);
              r = _out419;
              resultingOwnership = _out420;
              readIdents = _out421;
            }
          } else if (_source106.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2398___mcc_h284 = _source106.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2399___mcc_h287 = _source106.dtor_TypeArg_a0;
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
        } else if (_source98.is_Tuple) {
          Dafny.ISequence<DAST._IType> _2400___mcc_h290 = _source98.dtor_Tuple_a0;
          DAST._IType _source108 = _2239___mcc_h1;
          if (_source108.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2401___mcc_h294 = _source108.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2402___mcc_h295 = _source108.dtor_typeArgs;
            DAST._IResolvedType _2403___mcc_h296 = _source108.dtor_resolved;
            DAST._IResolvedType _source109 = _2403___mcc_h296;
            if (_source109.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2404___mcc_h300 = _source109.dtor_path;
              {
                RAST._IExpr _out428;
                DCOMP._IOwnership _out429;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out428, out _out429, out _out430);
                r = _out428;
                resultingOwnership = _out429;
                readIdents = _out430;
              }
            } else if (_source109.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2405___mcc_h302 = _source109.dtor_path;
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
              DAST._IType _2406___mcc_h304 = _source109.dtor_baseType;
              DAST._INewtypeRange _2407___mcc_h305 = _source109.dtor_range;
              bool _2408___mcc_h306 = _source109.dtor_erase;
              bool _2409_erase = _2408___mcc_h306;
              DAST._INewtypeRange _2410_range = _2407___mcc_h305;
              DAST._IType _2411_b = _2406___mcc_h304;
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
          } else if (_source108.is_Nullable) {
            DAST._IType _2412___mcc_h310 = _source108.dtor_Nullable_a0;
            {
              RAST._IExpr _out437;
              DCOMP._IOwnership _out438;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out437, out _out438, out _out439);
              r = _out437;
              resultingOwnership = _out438;
              readIdents = _out439;
            }
          } else if (_source108.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2413___mcc_h312 = _source108.dtor_Tuple_a0;
            {
              RAST._IExpr _out440;
              DCOMP._IOwnership _out441;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out440, out _out441, out _out442);
              r = _out440;
              resultingOwnership = _out441;
              readIdents = _out442;
            }
          } else if (_source108.is_Array) {
            DAST._IType _2414___mcc_h314 = _source108.dtor_element;
            BigInteger _2415___mcc_h315 = _source108.dtor_dims;
            {
              RAST._IExpr _out443;
              DCOMP._IOwnership _out444;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out443, out _out444, out _out445);
              r = _out443;
              resultingOwnership = _out444;
              readIdents = _out445;
            }
          } else if (_source108.is_Seq) {
            DAST._IType _2416___mcc_h318 = _source108.dtor_element;
            {
              RAST._IExpr _out446;
              DCOMP._IOwnership _out447;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out446, out _out447, out _out448);
              r = _out446;
              resultingOwnership = _out447;
              readIdents = _out448;
            }
          } else if (_source108.is_Set) {
            DAST._IType _2417___mcc_h320 = _source108.dtor_element;
            {
              RAST._IExpr _out449;
              DCOMP._IOwnership _out450;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out449, out _out450, out _out451);
              r = _out449;
              resultingOwnership = _out450;
              readIdents = _out451;
            }
          } else if (_source108.is_Multiset) {
            DAST._IType _2418___mcc_h322 = _source108.dtor_element;
            {
              RAST._IExpr _out452;
              DCOMP._IOwnership _out453;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out452, out _out453, out _out454);
              r = _out452;
              resultingOwnership = _out453;
              readIdents = _out454;
            }
          } else if (_source108.is_Map) {
            DAST._IType _2419___mcc_h324 = _source108.dtor_key;
            DAST._IType _2420___mcc_h325 = _source108.dtor_value;
            {
              RAST._IExpr _out455;
              DCOMP._IOwnership _out456;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out455, out _out456, out _out457);
              r = _out455;
              resultingOwnership = _out456;
              readIdents = _out457;
            }
          } else if (_source108.is_SetBuilder) {
            DAST._IType _2421___mcc_h328 = _source108.dtor_element;
            {
              RAST._IExpr _out458;
              DCOMP._IOwnership _out459;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out458, out _out459, out _out460);
              r = _out458;
              resultingOwnership = _out459;
              readIdents = _out460;
            }
          } else if (_source108.is_MapBuilder) {
            DAST._IType _2422___mcc_h330 = _source108.dtor_key;
            DAST._IType _2423___mcc_h331 = _source108.dtor_value;
            {
              RAST._IExpr _out461;
              DCOMP._IOwnership _out462;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out463;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out461, out _out462, out _out463);
              r = _out461;
              resultingOwnership = _out462;
              readIdents = _out463;
            }
          } else if (_source108.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2424___mcc_h334 = _source108.dtor_args;
            DAST._IType _2425___mcc_h335 = _source108.dtor_result;
            {
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out464, out _out465, out _out466);
              r = _out464;
              resultingOwnership = _out465;
              readIdents = _out466;
            }
          } else if (_source108.is_Primitive) {
            DAST._IPrimitive _2426___mcc_h338 = _source108.dtor_Primitive_a0;
            {
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out467, out _out468, out _out469);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _out469;
            }
          } else if (_source108.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2427___mcc_h340 = _source108.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2428___mcc_h342 = _source108.dtor_TypeArg_a0;
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
        } else if (_source98.is_Array) {
          DAST._IType _2429___mcc_h344 = _source98.dtor_element;
          BigInteger _2430___mcc_h345 = _source98.dtor_dims;
          DAST._IType _source110 = _2239___mcc_h1;
          if (_source110.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2431___mcc_h352 = _source110.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2432___mcc_h353 = _source110.dtor_typeArgs;
            DAST._IResolvedType _2433___mcc_h354 = _source110.dtor_resolved;
            DAST._IResolvedType _source111 = _2433___mcc_h354;
            if (_source111.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2434___mcc_h358 = _source111.dtor_path;
              {
                RAST._IExpr _out476;
                DCOMP._IOwnership _out477;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out478;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out476, out _out477, out _out478);
                r = _out476;
                resultingOwnership = _out477;
                readIdents = _out478;
              }
            } else if (_source111.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2435___mcc_h360 = _source111.dtor_path;
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
              DAST._IType _2436___mcc_h362 = _source111.dtor_baseType;
              DAST._INewtypeRange _2437___mcc_h363 = _source111.dtor_range;
              bool _2438___mcc_h364 = _source111.dtor_erase;
              bool _2439_erase = _2438___mcc_h364;
              DAST._INewtypeRange _2440_range = _2437___mcc_h363;
              DAST._IType _2441_b = _2436___mcc_h362;
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
          } else if (_source110.is_Nullable) {
            DAST._IType _2442___mcc_h368 = _source110.dtor_Nullable_a0;
            {
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out485, out _out486, out _out487);
              r = _out485;
              resultingOwnership = _out486;
              readIdents = _out487;
            }
          } else if (_source110.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2443___mcc_h370 = _source110.dtor_Tuple_a0;
            {
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out488, out _out489, out _out490);
              r = _out488;
              resultingOwnership = _out489;
              readIdents = _out490;
            }
          } else if (_source110.is_Array) {
            DAST._IType _2444___mcc_h372 = _source110.dtor_element;
            BigInteger _2445___mcc_h373 = _source110.dtor_dims;
            {
              RAST._IExpr _out491;
              DCOMP._IOwnership _out492;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out491, out _out492, out _out493);
              r = _out491;
              resultingOwnership = _out492;
              readIdents = _out493;
            }
          } else if (_source110.is_Seq) {
            DAST._IType _2446___mcc_h376 = _source110.dtor_element;
            {
              RAST._IExpr _out494;
              DCOMP._IOwnership _out495;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out494, out _out495, out _out496);
              r = _out494;
              resultingOwnership = _out495;
              readIdents = _out496;
            }
          } else if (_source110.is_Set) {
            DAST._IType _2447___mcc_h378 = _source110.dtor_element;
            {
              RAST._IExpr _out497;
              DCOMP._IOwnership _out498;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out497, out _out498, out _out499);
              r = _out497;
              resultingOwnership = _out498;
              readIdents = _out499;
            }
          } else if (_source110.is_Multiset) {
            DAST._IType _2448___mcc_h380 = _source110.dtor_element;
            {
              RAST._IExpr _out500;
              DCOMP._IOwnership _out501;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out502;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out500, out _out501, out _out502);
              r = _out500;
              resultingOwnership = _out501;
              readIdents = _out502;
            }
          } else if (_source110.is_Map) {
            DAST._IType _2449___mcc_h382 = _source110.dtor_key;
            DAST._IType _2450___mcc_h383 = _source110.dtor_value;
            {
              RAST._IExpr _out503;
              DCOMP._IOwnership _out504;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out503, out _out504, out _out505);
              r = _out503;
              resultingOwnership = _out504;
              readIdents = _out505;
            }
          } else if (_source110.is_SetBuilder) {
            DAST._IType _2451___mcc_h386 = _source110.dtor_element;
            {
              RAST._IExpr _out506;
              DCOMP._IOwnership _out507;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out506, out _out507, out _out508);
              r = _out506;
              resultingOwnership = _out507;
              readIdents = _out508;
            }
          } else if (_source110.is_MapBuilder) {
            DAST._IType _2452___mcc_h388 = _source110.dtor_key;
            DAST._IType _2453___mcc_h389 = _source110.dtor_value;
            {
              RAST._IExpr _out509;
              DCOMP._IOwnership _out510;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out509, out _out510, out _out511);
              r = _out509;
              resultingOwnership = _out510;
              readIdents = _out511;
            }
          } else if (_source110.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2454___mcc_h392 = _source110.dtor_args;
            DAST._IType _2455___mcc_h393 = _source110.dtor_result;
            {
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out512, out _out513, out _out514);
              r = _out512;
              resultingOwnership = _out513;
              readIdents = _out514;
            }
          } else if (_source110.is_Primitive) {
            DAST._IPrimitive _2456___mcc_h396 = _source110.dtor_Primitive_a0;
            {
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out515, out _out516, out _out517);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _out517;
            }
          } else if (_source110.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2457___mcc_h398 = _source110.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2458___mcc_h400 = _source110.dtor_TypeArg_a0;
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
        } else if (_source98.is_Seq) {
          DAST._IType _2459___mcc_h402 = _source98.dtor_element;
          DAST._IType _source112 = _2239___mcc_h1;
          if (_source112.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2460___mcc_h406 = _source112.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2461___mcc_h407 = _source112.dtor_typeArgs;
            DAST._IResolvedType _2462___mcc_h408 = _source112.dtor_resolved;
            DAST._IResolvedType _source113 = _2462___mcc_h408;
            if (_source113.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2463___mcc_h412 = _source113.dtor_path;
              {
                RAST._IExpr _out524;
                DCOMP._IOwnership _out525;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out526;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out524, out _out525, out _out526);
                r = _out524;
                resultingOwnership = _out525;
                readIdents = _out526;
              }
            } else if (_source113.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2464___mcc_h414 = _source113.dtor_path;
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
              DAST._IType _2465___mcc_h416 = _source113.dtor_baseType;
              DAST._INewtypeRange _2466___mcc_h417 = _source113.dtor_range;
              bool _2467___mcc_h418 = _source113.dtor_erase;
              bool _2468_erase = _2467___mcc_h418;
              DAST._INewtypeRange _2469_range = _2466___mcc_h417;
              DAST._IType _2470_b = _2465___mcc_h416;
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
          } else if (_source112.is_Nullable) {
            DAST._IType _2471___mcc_h422 = _source112.dtor_Nullable_a0;
            {
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out533, out _out534, out _out535);
              r = _out533;
              resultingOwnership = _out534;
              readIdents = _out535;
            }
          } else if (_source112.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2472___mcc_h424 = _source112.dtor_Tuple_a0;
            {
              RAST._IExpr _out536;
              DCOMP._IOwnership _out537;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out536, out _out537, out _out538);
              r = _out536;
              resultingOwnership = _out537;
              readIdents = _out538;
            }
          } else if (_source112.is_Array) {
            DAST._IType _2473___mcc_h426 = _source112.dtor_element;
            BigInteger _2474___mcc_h427 = _source112.dtor_dims;
            {
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out539, out _out540, out _out541);
              r = _out539;
              resultingOwnership = _out540;
              readIdents = _out541;
            }
          } else if (_source112.is_Seq) {
            DAST._IType _2475___mcc_h430 = _source112.dtor_element;
            {
              RAST._IExpr _out542;
              DCOMP._IOwnership _out543;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out542, out _out543, out _out544);
              r = _out542;
              resultingOwnership = _out543;
              readIdents = _out544;
            }
          } else if (_source112.is_Set) {
            DAST._IType _2476___mcc_h432 = _source112.dtor_element;
            {
              RAST._IExpr _out545;
              DCOMP._IOwnership _out546;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out545, out _out546, out _out547);
              r = _out545;
              resultingOwnership = _out546;
              readIdents = _out547;
            }
          } else if (_source112.is_Multiset) {
            DAST._IType _2477___mcc_h434 = _source112.dtor_element;
            {
              RAST._IExpr _out548;
              DCOMP._IOwnership _out549;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out548, out _out549, out _out550);
              r = _out548;
              resultingOwnership = _out549;
              readIdents = _out550;
            }
          } else if (_source112.is_Map) {
            DAST._IType _2478___mcc_h436 = _source112.dtor_key;
            DAST._IType _2479___mcc_h437 = _source112.dtor_value;
            {
              RAST._IExpr _out551;
              DCOMP._IOwnership _out552;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out551, out _out552, out _out553);
              r = _out551;
              resultingOwnership = _out552;
              readIdents = _out553;
            }
          } else if (_source112.is_SetBuilder) {
            DAST._IType _2480___mcc_h440 = _source112.dtor_element;
            {
              RAST._IExpr _out554;
              DCOMP._IOwnership _out555;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out554, out _out555, out _out556);
              r = _out554;
              resultingOwnership = _out555;
              readIdents = _out556;
            }
          } else if (_source112.is_MapBuilder) {
            DAST._IType _2481___mcc_h442 = _source112.dtor_key;
            DAST._IType _2482___mcc_h443 = _source112.dtor_value;
            {
              RAST._IExpr _out557;
              DCOMP._IOwnership _out558;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out557, out _out558, out _out559);
              r = _out557;
              resultingOwnership = _out558;
              readIdents = _out559;
            }
          } else if (_source112.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2483___mcc_h446 = _source112.dtor_args;
            DAST._IType _2484___mcc_h447 = _source112.dtor_result;
            {
              RAST._IExpr _out560;
              DCOMP._IOwnership _out561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out560, out _out561, out _out562);
              r = _out560;
              resultingOwnership = _out561;
              readIdents = _out562;
            }
          } else if (_source112.is_Primitive) {
            DAST._IPrimitive _2485___mcc_h450 = _source112.dtor_Primitive_a0;
            {
              RAST._IExpr _out563;
              DCOMP._IOwnership _out564;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out563, out _out564, out _out565);
              r = _out563;
              resultingOwnership = _out564;
              readIdents = _out565;
            }
          } else if (_source112.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2486___mcc_h452 = _source112.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2487___mcc_h454 = _source112.dtor_TypeArg_a0;
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
        } else if (_source98.is_Set) {
          DAST._IType _2488___mcc_h456 = _source98.dtor_element;
          DAST._IType _source114 = _2239___mcc_h1;
          if (_source114.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2489___mcc_h460 = _source114.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2490___mcc_h461 = _source114.dtor_typeArgs;
            DAST._IResolvedType _2491___mcc_h462 = _source114.dtor_resolved;
            DAST._IResolvedType _source115 = _2491___mcc_h462;
            if (_source115.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2492___mcc_h466 = _source115.dtor_path;
              {
                RAST._IExpr _out572;
                DCOMP._IOwnership _out573;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out572, out _out573, out _out574);
                r = _out572;
                resultingOwnership = _out573;
                readIdents = _out574;
              }
            } else if (_source115.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2493___mcc_h468 = _source115.dtor_path;
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
              DAST._IType _2494___mcc_h470 = _source115.dtor_baseType;
              DAST._INewtypeRange _2495___mcc_h471 = _source115.dtor_range;
              bool _2496___mcc_h472 = _source115.dtor_erase;
              bool _2497_erase = _2496___mcc_h472;
              DAST._INewtypeRange _2498_range = _2495___mcc_h471;
              DAST._IType _2499_b = _2494___mcc_h470;
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
          } else if (_source114.is_Nullable) {
            DAST._IType _2500___mcc_h476 = _source114.dtor_Nullable_a0;
            {
              RAST._IExpr _out581;
              DCOMP._IOwnership _out582;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out583;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out581, out _out582, out _out583);
              r = _out581;
              resultingOwnership = _out582;
              readIdents = _out583;
            }
          } else if (_source114.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2501___mcc_h478 = _source114.dtor_Tuple_a0;
            {
              RAST._IExpr _out584;
              DCOMP._IOwnership _out585;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out584, out _out585, out _out586);
              r = _out584;
              resultingOwnership = _out585;
              readIdents = _out586;
            }
          } else if (_source114.is_Array) {
            DAST._IType _2502___mcc_h480 = _source114.dtor_element;
            BigInteger _2503___mcc_h481 = _source114.dtor_dims;
            {
              RAST._IExpr _out587;
              DCOMP._IOwnership _out588;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out587, out _out588, out _out589);
              r = _out587;
              resultingOwnership = _out588;
              readIdents = _out589;
            }
          } else if (_source114.is_Seq) {
            DAST._IType _2504___mcc_h484 = _source114.dtor_element;
            {
              RAST._IExpr _out590;
              DCOMP._IOwnership _out591;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out590, out _out591, out _out592);
              r = _out590;
              resultingOwnership = _out591;
              readIdents = _out592;
            }
          } else if (_source114.is_Set) {
            DAST._IType _2505___mcc_h486 = _source114.dtor_element;
            {
              RAST._IExpr _out593;
              DCOMP._IOwnership _out594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out595;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out593, out _out594, out _out595);
              r = _out593;
              resultingOwnership = _out594;
              readIdents = _out595;
            }
          } else if (_source114.is_Multiset) {
            DAST._IType _2506___mcc_h488 = _source114.dtor_element;
            {
              RAST._IExpr _out596;
              DCOMP._IOwnership _out597;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out596, out _out597, out _out598);
              r = _out596;
              resultingOwnership = _out597;
              readIdents = _out598;
            }
          } else if (_source114.is_Map) {
            DAST._IType _2507___mcc_h490 = _source114.dtor_key;
            DAST._IType _2508___mcc_h491 = _source114.dtor_value;
            {
              RAST._IExpr _out599;
              DCOMP._IOwnership _out600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out601;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out599, out _out600, out _out601);
              r = _out599;
              resultingOwnership = _out600;
              readIdents = _out601;
            }
          } else if (_source114.is_SetBuilder) {
            DAST._IType _2509___mcc_h494 = _source114.dtor_element;
            {
              RAST._IExpr _out602;
              DCOMP._IOwnership _out603;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out602, out _out603, out _out604);
              r = _out602;
              resultingOwnership = _out603;
              readIdents = _out604;
            }
          } else if (_source114.is_MapBuilder) {
            DAST._IType _2510___mcc_h496 = _source114.dtor_key;
            DAST._IType _2511___mcc_h497 = _source114.dtor_value;
            {
              RAST._IExpr _out605;
              DCOMP._IOwnership _out606;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out605, out _out606, out _out607);
              r = _out605;
              resultingOwnership = _out606;
              readIdents = _out607;
            }
          } else if (_source114.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2512___mcc_h500 = _source114.dtor_args;
            DAST._IType _2513___mcc_h501 = _source114.dtor_result;
            {
              RAST._IExpr _out608;
              DCOMP._IOwnership _out609;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out608, out _out609, out _out610);
              r = _out608;
              resultingOwnership = _out609;
              readIdents = _out610;
            }
          } else if (_source114.is_Primitive) {
            DAST._IPrimitive _2514___mcc_h504 = _source114.dtor_Primitive_a0;
            {
              RAST._IExpr _out611;
              DCOMP._IOwnership _out612;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out611, out _out612, out _out613);
              r = _out611;
              resultingOwnership = _out612;
              readIdents = _out613;
            }
          } else if (_source114.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2515___mcc_h506 = _source114.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2516___mcc_h508 = _source114.dtor_TypeArg_a0;
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
        } else if (_source98.is_Multiset) {
          DAST._IType _2517___mcc_h510 = _source98.dtor_element;
          DAST._IType _source116 = _2239___mcc_h1;
          if (_source116.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2518___mcc_h514 = _source116.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2519___mcc_h515 = _source116.dtor_typeArgs;
            DAST._IResolvedType _2520___mcc_h516 = _source116.dtor_resolved;
            DAST._IResolvedType _source117 = _2520___mcc_h516;
            if (_source117.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2521___mcc_h520 = _source117.dtor_path;
              {
                RAST._IExpr _out620;
                DCOMP._IOwnership _out621;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out620, out _out621, out _out622);
                r = _out620;
                resultingOwnership = _out621;
                readIdents = _out622;
              }
            } else if (_source117.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2522___mcc_h522 = _source117.dtor_path;
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
              DAST._IType _2523___mcc_h524 = _source117.dtor_baseType;
              DAST._INewtypeRange _2524___mcc_h525 = _source117.dtor_range;
              bool _2525___mcc_h526 = _source117.dtor_erase;
              bool _2526_erase = _2525___mcc_h526;
              DAST._INewtypeRange _2527_range = _2524___mcc_h525;
              DAST._IType _2528_b = _2523___mcc_h524;
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
          } else if (_source116.is_Nullable) {
            DAST._IType _2529___mcc_h530 = _source116.dtor_Nullable_a0;
            {
              RAST._IExpr _out629;
              DCOMP._IOwnership _out630;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out631;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out629, out _out630, out _out631);
              r = _out629;
              resultingOwnership = _out630;
              readIdents = _out631;
            }
          } else if (_source116.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2530___mcc_h532 = _source116.dtor_Tuple_a0;
            {
              RAST._IExpr _out632;
              DCOMP._IOwnership _out633;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out632, out _out633, out _out634);
              r = _out632;
              resultingOwnership = _out633;
              readIdents = _out634;
            }
          } else if (_source116.is_Array) {
            DAST._IType _2531___mcc_h534 = _source116.dtor_element;
            BigInteger _2532___mcc_h535 = _source116.dtor_dims;
            {
              RAST._IExpr _out635;
              DCOMP._IOwnership _out636;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out635, out _out636, out _out637);
              r = _out635;
              resultingOwnership = _out636;
              readIdents = _out637;
            }
          } else if (_source116.is_Seq) {
            DAST._IType _2533___mcc_h538 = _source116.dtor_element;
            {
              RAST._IExpr _out638;
              DCOMP._IOwnership _out639;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out638, out _out639, out _out640);
              r = _out638;
              resultingOwnership = _out639;
              readIdents = _out640;
            }
          } else if (_source116.is_Set) {
            DAST._IType _2534___mcc_h540 = _source116.dtor_element;
            {
              RAST._IExpr _out641;
              DCOMP._IOwnership _out642;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out641, out _out642, out _out643);
              r = _out641;
              resultingOwnership = _out642;
              readIdents = _out643;
            }
          } else if (_source116.is_Multiset) {
            DAST._IType _2535___mcc_h542 = _source116.dtor_element;
            {
              RAST._IExpr _out644;
              DCOMP._IOwnership _out645;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out646;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out644, out _out645, out _out646);
              r = _out644;
              resultingOwnership = _out645;
              readIdents = _out646;
            }
          } else if (_source116.is_Map) {
            DAST._IType _2536___mcc_h544 = _source116.dtor_key;
            DAST._IType _2537___mcc_h545 = _source116.dtor_value;
            {
              RAST._IExpr _out647;
              DCOMP._IOwnership _out648;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out647, out _out648, out _out649);
              r = _out647;
              resultingOwnership = _out648;
              readIdents = _out649;
            }
          } else if (_source116.is_SetBuilder) {
            DAST._IType _2538___mcc_h548 = _source116.dtor_element;
            {
              RAST._IExpr _out650;
              DCOMP._IOwnership _out651;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out652;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out650, out _out651, out _out652);
              r = _out650;
              resultingOwnership = _out651;
              readIdents = _out652;
            }
          } else if (_source116.is_MapBuilder) {
            DAST._IType _2539___mcc_h550 = _source116.dtor_key;
            DAST._IType _2540___mcc_h551 = _source116.dtor_value;
            {
              RAST._IExpr _out653;
              DCOMP._IOwnership _out654;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out653, out _out654, out _out655);
              r = _out653;
              resultingOwnership = _out654;
              readIdents = _out655;
            }
          } else if (_source116.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2541___mcc_h554 = _source116.dtor_args;
            DAST._IType _2542___mcc_h555 = _source116.dtor_result;
            {
              RAST._IExpr _out656;
              DCOMP._IOwnership _out657;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out656, out _out657, out _out658);
              r = _out656;
              resultingOwnership = _out657;
              readIdents = _out658;
            }
          } else if (_source116.is_Primitive) {
            DAST._IPrimitive _2543___mcc_h558 = _source116.dtor_Primitive_a0;
            {
              RAST._IExpr _out659;
              DCOMP._IOwnership _out660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out659, out _out660, out _out661);
              r = _out659;
              resultingOwnership = _out660;
              readIdents = _out661;
            }
          } else if (_source116.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2544___mcc_h560 = _source116.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2545___mcc_h562 = _source116.dtor_TypeArg_a0;
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
        } else if (_source98.is_Map) {
          DAST._IType _2546___mcc_h564 = _source98.dtor_key;
          DAST._IType _2547___mcc_h565 = _source98.dtor_value;
          DAST._IType _source118 = _2239___mcc_h1;
          if (_source118.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2548___mcc_h572 = _source118.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2549___mcc_h573 = _source118.dtor_typeArgs;
            DAST._IResolvedType _2550___mcc_h574 = _source118.dtor_resolved;
            DAST._IResolvedType _source119 = _2550___mcc_h574;
            if (_source119.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2551___mcc_h578 = _source119.dtor_path;
              {
                RAST._IExpr _out668;
                DCOMP._IOwnership _out669;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out670;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out668, out _out669, out _out670);
                r = _out668;
                resultingOwnership = _out669;
                readIdents = _out670;
              }
            } else if (_source119.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2552___mcc_h580 = _source119.dtor_path;
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
              DAST._IType _2553___mcc_h582 = _source119.dtor_baseType;
              DAST._INewtypeRange _2554___mcc_h583 = _source119.dtor_range;
              bool _2555___mcc_h584 = _source119.dtor_erase;
              bool _2556_erase = _2555___mcc_h584;
              DAST._INewtypeRange _2557_range = _2554___mcc_h583;
              DAST._IType _2558_b = _2553___mcc_h582;
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
          } else if (_source118.is_Nullable) {
            DAST._IType _2559___mcc_h588 = _source118.dtor_Nullable_a0;
            {
              RAST._IExpr _out677;
              DCOMP._IOwnership _out678;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out677, out _out678, out _out679);
              r = _out677;
              resultingOwnership = _out678;
              readIdents = _out679;
            }
          } else if (_source118.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2560___mcc_h590 = _source118.dtor_Tuple_a0;
            {
              RAST._IExpr _out680;
              DCOMP._IOwnership _out681;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out682;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out680, out _out681, out _out682);
              r = _out680;
              resultingOwnership = _out681;
              readIdents = _out682;
            }
          } else if (_source118.is_Array) {
            DAST._IType _2561___mcc_h592 = _source118.dtor_element;
            BigInteger _2562___mcc_h593 = _source118.dtor_dims;
            {
              RAST._IExpr _out683;
              DCOMP._IOwnership _out684;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out685;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out683, out _out684, out _out685);
              r = _out683;
              resultingOwnership = _out684;
              readIdents = _out685;
            }
          } else if (_source118.is_Seq) {
            DAST._IType _2563___mcc_h596 = _source118.dtor_element;
            {
              RAST._IExpr _out686;
              DCOMP._IOwnership _out687;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out688;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out686, out _out687, out _out688);
              r = _out686;
              resultingOwnership = _out687;
              readIdents = _out688;
            }
          } else if (_source118.is_Set) {
            DAST._IType _2564___mcc_h598 = _source118.dtor_element;
            {
              RAST._IExpr _out689;
              DCOMP._IOwnership _out690;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out689, out _out690, out _out691);
              r = _out689;
              resultingOwnership = _out690;
              readIdents = _out691;
            }
          } else if (_source118.is_Multiset) {
            DAST._IType _2565___mcc_h600 = _source118.dtor_element;
            {
              RAST._IExpr _out692;
              DCOMP._IOwnership _out693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out694;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out692, out _out693, out _out694);
              r = _out692;
              resultingOwnership = _out693;
              readIdents = _out694;
            }
          } else if (_source118.is_Map) {
            DAST._IType _2566___mcc_h602 = _source118.dtor_key;
            DAST._IType _2567___mcc_h603 = _source118.dtor_value;
            {
              RAST._IExpr _out695;
              DCOMP._IOwnership _out696;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out697;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out695, out _out696, out _out697);
              r = _out695;
              resultingOwnership = _out696;
              readIdents = _out697;
            }
          } else if (_source118.is_SetBuilder) {
            DAST._IType _2568___mcc_h606 = _source118.dtor_element;
            {
              RAST._IExpr _out698;
              DCOMP._IOwnership _out699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out698, out _out699, out _out700);
              r = _out698;
              resultingOwnership = _out699;
              readIdents = _out700;
            }
          } else if (_source118.is_MapBuilder) {
            DAST._IType _2569___mcc_h608 = _source118.dtor_key;
            DAST._IType _2570___mcc_h609 = _source118.dtor_value;
            {
              RAST._IExpr _out701;
              DCOMP._IOwnership _out702;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out703;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out701, out _out702, out _out703);
              r = _out701;
              resultingOwnership = _out702;
              readIdents = _out703;
            }
          } else if (_source118.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2571___mcc_h612 = _source118.dtor_args;
            DAST._IType _2572___mcc_h613 = _source118.dtor_result;
            {
              RAST._IExpr _out704;
              DCOMP._IOwnership _out705;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out706;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out704, out _out705, out _out706);
              r = _out704;
              resultingOwnership = _out705;
              readIdents = _out706;
            }
          } else if (_source118.is_Primitive) {
            DAST._IPrimitive _2573___mcc_h616 = _source118.dtor_Primitive_a0;
            {
              RAST._IExpr _out707;
              DCOMP._IOwnership _out708;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out709;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out707, out _out708, out _out709);
              r = _out707;
              resultingOwnership = _out708;
              readIdents = _out709;
            }
          } else if (_source118.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2574___mcc_h618 = _source118.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2575___mcc_h620 = _source118.dtor_TypeArg_a0;
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
        } else if (_source98.is_SetBuilder) {
          DAST._IType _2576___mcc_h622 = _source98.dtor_element;
          DAST._IType _source120 = _2239___mcc_h1;
          if (_source120.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2577___mcc_h626 = _source120.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2578___mcc_h627 = _source120.dtor_typeArgs;
            DAST._IResolvedType _2579___mcc_h628 = _source120.dtor_resolved;
            DAST._IResolvedType _source121 = _2579___mcc_h628;
            if (_source121.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2580___mcc_h632 = _source121.dtor_path;
              {
                RAST._IExpr _out716;
                DCOMP._IOwnership _out717;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out718;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out716, out _out717, out _out718);
                r = _out716;
                resultingOwnership = _out717;
                readIdents = _out718;
              }
            } else if (_source121.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2581___mcc_h634 = _source121.dtor_path;
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
              DAST._IType _2582___mcc_h636 = _source121.dtor_baseType;
              DAST._INewtypeRange _2583___mcc_h637 = _source121.dtor_range;
              bool _2584___mcc_h638 = _source121.dtor_erase;
              bool _2585_erase = _2584___mcc_h638;
              DAST._INewtypeRange _2586_range = _2583___mcc_h637;
              DAST._IType _2587_b = _2582___mcc_h636;
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
          } else if (_source120.is_Nullable) {
            DAST._IType _2588___mcc_h642 = _source120.dtor_Nullable_a0;
            {
              RAST._IExpr _out725;
              DCOMP._IOwnership _out726;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out727;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out725, out _out726, out _out727);
              r = _out725;
              resultingOwnership = _out726;
              readIdents = _out727;
            }
          } else if (_source120.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2589___mcc_h644 = _source120.dtor_Tuple_a0;
            {
              RAST._IExpr _out728;
              DCOMP._IOwnership _out729;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out730;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out728, out _out729, out _out730);
              r = _out728;
              resultingOwnership = _out729;
              readIdents = _out730;
            }
          } else if (_source120.is_Array) {
            DAST._IType _2590___mcc_h646 = _source120.dtor_element;
            BigInteger _2591___mcc_h647 = _source120.dtor_dims;
            {
              RAST._IExpr _out731;
              DCOMP._IOwnership _out732;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out733;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out731, out _out732, out _out733);
              r = _out731;
              resultingOwnership = _out732;
              readIdents = _out733;
            }
          } else if (_source120.is_Seq) {
            DAST._IType _2592___mcc_h650 = _source120.dtor_element;
            {
              RAST._IExpr _out734;
              DCOMP._IOwnership _out735;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out734, out _out735, out _out736);
              r = _out734;
              resultingOwnership = _out735;
              readIdents = _out736;
            }
          } else if (_source120.is_Set) {
            DAST._IType _2593___mcc_h652 = _source120.dtor_element;
            {
              RAST._IExpr _out737;
              DCOMP._IOwnership _out738;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out739;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out737, out _out738, out _out739);
              r = _out737;
              resultingOwnership = _out738;
              readIdents = _out739;
            }
          } else if (_source120.is_Multiset) {
            DAST._IType _2594___mcc_h654 = _source120.dtor_element;
            {
              RAST._IExpr _out740;
              DCOMP._IOwnership _out741;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out742;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out740, out _out741, out _out742);
              r = _out740;
              resultingOwnership = _out741;
              readIdents = _out742;
            }
          } else if (_source120.is_Map) {
            DAST._IType _2595___mcc_h656 = _source120.dtor_key;
            DAST._IType _2596___mcc_h657 = _source120.dtor_value;
            {
              RAST._IExpr _out743;
              DCOMP._IOwnership _out744;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out745;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out743, out _out744, out _out745);
              r = _out743;
              resultingOwnership = _out744;
              readIdents = _out745;
            }
          } else if (_source120.is_SetBuilder) {
            DAST._IType _2597___mcc_h660 = _source120.dtor_element;
            {
              RAST._IExpr _out746;
              DCOMP._IOwnership _out747;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out746, out _out747, out _out748);
              r = _out746;
              resultingOwnership = _out747;
              readIdents = _out748;
            }
          } else if (_source120.is_MapBuilder) {
            DAST._IType _2598___mcc_h662 = _source120.dtor_key;
            DAST._IType _2599___mcc_h663 = _source120.dtor_value;
            {
              RAST._IExpr _out749;
              DCOMP._IOwnership _out750;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out751;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out749, out _out750, out _out751);
              r = _out749;
              resultingOwnership = _out750;
              readIdents = _out751;
            }
          } else if (_source120.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2600___mcc_h666 = _source120.dtor_args;
            DAST._IType _2601___mcc_h667 = _source120.dtor_result;
            {
              RAST._IExpr _out752;
              DCOMP._IOwnership _out753;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out754;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out752, out _out753, out _out754);
              r = _out752;
              resultingOwnership = _out753;
              readIdents = _out754;
            }
          } else if (_source120.is_Primitive) {
            DAST._IPrimitive _2602___mcc_h670 = _source120.dtor_Primitive_a0;
            {
              RAST._IExpr _out755;
              DCOMP._IOwnership _out756;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out757;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out755, out _out756, out _out757);
              r = _out755;
              resultingOwnership = _out756;
              readIdents = _out757;
            }
          } else if (_source120.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2603___mcc_h672 = _source120.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2604___mcc_h674 = _source120.dtor_TypeArg_a0;
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
        } else if (_source98.is_MapBuilder) {
          DAST._IType _2605___mcc_h676 = _source98.dtor_key;
          DAST._IType _2606___mcc_h677 = _source98.dtor_value;
          DAST._IType _source122 = _2239___mcc_h1;
          if (_source122.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2607___mcc_h684 = _source122.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2608___mcc_h685 = _source122.dtor_typeArgs;
            DAST._IResolvedType _2609___mcc_h686 = _source122.dtor_resolved;
            DAST._IResolvedType _source123 = _2609___mcc_h686;
            if (_source123.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2610___mcc_h690 = _source123.dtor_path;
              {
                RAST._IExpr _out764;
                DCOMP._IOwnership _out765;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out766;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out764, out _out765, out _out766);
                r = _out764;
                resultingOwnership = _out765;
                readIdents = _out766;
              }
            } else if (_source123.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2611___mcc_h692 = _source123.dtor_path;
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
              DAST._IType _2612___mcc_h694 = _source123.dtor_baseType;
              DAST._INewtypeRange _2613___mcc_h695 = _source123.dtor_range;
              bool _2614___mcc_h696 = _source123.dtor_erase;
              bool _2615_erase = _2614___mcc_h696;
              DAST._INewtypeRange _2616_range = _2613___mcc_h695;
              DAST._IType _2617_b = _2612___mcc_h694;
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
          } else if (_source122.is_Nullable) {
            DAST._IType _2618___mcc_h700 = _source122.dtor_Nullable_a0;
            {
              RAST._IExpr _out773;
              DCOMP._IOwnership _out774;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out775;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out773, out _out774, out _out775);
              r = _out773;
              resultingOwnership = _out774;
              readIdents = _out775;
            }
          } else if (_source122.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2619___mcc_h702 = _source122.dtor_Tuple_a0;
            {
              RAST._IExpr _out776;
              DCOMP._IOwnership _out777;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out778;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out776, out _out777, out _out778);
              r = _out776;
              resultingOwnership = _out777;
              readIdents = _out778;
            }
          } else if (_source122.is_Array) {
            DAST._IType _2620___mcc_h704 = _source122.dtor_element;
            BigInteger _2621___mcc_h705 = _source122.dtor_dims;
            {
              RAST._IExpr _out779;
              DCOMP._IOwnership _out780;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out779, out _out780, out _out781);
              r = _out779;
              resultingOwnership = _out780;
              readIdents = _out781;
            }
          } else if (_source122.is_Seq) {
            DAST._IType _2622___mcc_h708 = _source122.dtor_element;
            {
              RAST._IExpr _out782;
              DCOMP._IOwnership _out783;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out784;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out782, out _out783, out _out784);
              r = _out782;
              resultingOwnership = _out783;
              readIdents = _out784;
            }
          } else if (_source122.is_Set) {
            DAST._IType _2623___mcc_h710 = _source122.dtor_element;
            {
              RAST._IExpr _out785;
              DCOMP._IOwnership _out786;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out787;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out785, out _out786, out _out787);
              r = _out785;
              resultingOwnership = _out786;
              readIdents = _out787;
            }
          } else if (_source122.is_Multiset) {
            DAST._IType _2624___mcc_h712 = _source122.dtor_element;
            {
              RAST._IExpr _out788;
              DCOMP._IOwnership _out789;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out790;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out788, out _out789, out _out790);
              r = _out788;
              resultingOwnership = _out789;
              readIdents = _out790;
            }
          } else if (_source122.is_Map) {
            DAST._IType _2625___mcc_h714 = _source122.dtor_key;
            DAST._IType _2626___mcc_h715 = _source122.dtor_value;
            {
              RAST._IExpr _out791;
              DCOMP._IOwnership _out792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out791, out _out792, out _out793);
              r = _out791;
              resultingOwnership = _out792;
              readIdents = _out793;
            }
          } else if (_source122.is_SetBuilder) {
            DAST._IType _2627___mcc_h718 = _source122.dtor_element;
            {
              RAST._IExpr _out794;
              DCOMP._IOwnership _out795;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out796;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out794, out _out795, out _out796);
              r = _out794;
              resultingOwnership = _out795;
              readIdents = _out796;
            }
          } else if (_source122.is_MapBuilder) {
            DAST._IType _2628___mcc_h720 = _source122.dtor_key;
            DAST._IType _2629___mcc_h721 = _source122.dtor_value;
            {
              RAST._IExpr _out797;
              DCOMP._IOwnership _out798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out799;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out797, out _out798, out _out799);
              r = _out797;
              resultingOwnership = _out798;
              readIdents = _out799;
            }
          } else if (_source122.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2630___mcc_h724 = _source122.dtor_args;
            DAST._IType _2631___mcc_h725 = _source122.dtor_result;
            {
              RAST._IExpr _out800;
              DCOMP._IOwnership _out801;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out802;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out800, out _out801, out _out802);
              r = _out800;
              resultingOwnership = _out801;
              readIdents = _out802;
            }
          } else if (_source122.is_Primitive) {
            DAST._IPrimitive _2632___mcc_h728 = _source122.dtor_Primitive_a0;
            {
              RAST._IExpr _out803;
              DCOMP._IOwnership _out804;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out803, out _out804, out _out805);
              r = _out803;
              resultingOwnership = _out804;
              readIdents = _out805;
            }
          } else if (_source122.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2633___mcc_h730 = _source122.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2634___mcc_h732 = _source122.dtor_TypeArg_a0;
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
        } else if (_source98.is_Arrow) {
          Dafny.ISequence<DAST._IType> _2635___mcc_h734 = _source98.dtor_args;
          DAST._IType _2636___mcc_h735 = _source98.dtor_result;
          DAST._IType _source124 = _2239___mcc_h1;
          if (_source124.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2637___mcc_h742 = _source124.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2638___mcc_h743 = _source124.dtor_typeArgs;
            DAST._IResolvedType _2639___mcc_h744 = _source124.dtor_resolved;
            DAST._IResolvedType _source125 = _2639___mcc_h744;
            if (_source125.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2640___mcc_h748 = _source125.dtor_path;
              {
                RAST._IExpr _out812;
                DCOMP._IOwnership _out813;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out814;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out812, out _out813, out _out814);
                r = _out812;
                resultingOwnership = _out813;
                readIdents = _out814;
              }
            } else if (_source125.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2641___mcc_h750 = _source125.dtor_path;
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
              DAST._IType _2642___mcc_h752 = _source125.dtor_baseType;
              DAST._INewtypeRange _2643___mcc_h753 = _source125.dtor_range;
              bool _2644___mcc_h754 = _source125.dtor_erase;
              bool _2645_erase = _2644___mcc_h754;
              DAST._INewtypeRange _2646_range = _2643___mcc_h753;
              DAST._IType _2647_b = _2642___mcc_h752;
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
          } else if (_source124.is_Nullable) {
            DAST._IType _2648___mcc_h758 = _source124.dtor_Nullable_a0;
            {
              RAST._IExpr _out821;
              DCOMP._IOwnership _out822;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out823;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out821, out _out822, out _out823);
              r = _out821;
              resultingOwnership = _out822;
              readIdents = _out823;
            }
          } else if (_source124.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2649___mcc_h760 = _source124.dtor_Tuple_a0;
            {
              RAST._IExpr _out824;
              DCOMP._IOwnership _out825;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out824, out _out825, out _out826);
              r = _out824;
              resultingOwnership = _out825;
              readIdents = _out826;
            }
          } else if (_source124.is_Array) {
            DAST._IType _2650___mcc_h762 = _source124.dtor_element;
            BigInteger _2651___mcc_h763 = _source124.dtor_dims;
            {
              RAST._IExpr _out827;
              DCOMP._IOwnership _out828;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out829;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out827, out _out828, out _out829);
              r = _out827;
              resultingOwnership = _out828;
              readIdents = _out829;
            }
          } else if (_source124.is_Seq) {
            DAST._IType _2652___mcc_h766 = _source124.dtor_element;
            {
              RAST._IExpr _out830;
              DCOMP._IOwnership _out831;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out832;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out830, out _out831, out _out832);
              r = _out830;
              resultingOwnership = _out831;
              readIdents = _out832;
            }
          } else if (_source124.is_Set) {
            DAST._IType _2653___mcc_h768 = _source124.dtor_element;
            {
              RAST._IExpr _out833;
              DCOMP._IOwnership _out834;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out835;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out833, out _out834, out _out835);
              r = _out833;
              resultingOwnership = _out834;
              readIdents = _out835;
            }
          } else if (_source124.is_Multiset) {
            DAST._IType _2654___mcc_h770 = _source124.dtor_element;
            {
              RAST._IExpr _out836;
              DCOMP._IOwnership _out837;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out836, out _out837, out _out838);
              r = _out836;
              resultingOwnership = _out837;
              readIdents = _out838;
            }
          } else if (_source124.is_Map) {
            DAST._IType _2655___mcc_h772 = _source124.dtor_key;
            DAST._IType _2656___mcc_h773 = _source124.dtor_value;
            {
              RAST._IExpr _out839;
              DCOMP._IOwnership _out840;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out841;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out839, out _out840, out _out841);
              r = _out839;
              resultingOwnership = _out840;
              readIdents = _out841;
            }
          } else if (_source124.is_SetBuilder) {
            DAST._IType _2657___mcc_h776 = _source124.dtor_element;
            {
              RAST._IExpr _out842;
              DCOMP._IOwnership _out843;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out844;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out842, out _out843, out _out844);
              r = _out842;
              resultingOwnership = _out843;
              readIdents = _out844;
            }
          } else if (_source124.is_MapBuilder) {
            DAST._IType _2658___mcc_h778 = _source124.dtor_key;
            DAST._IType _2659___mcc_h779 = _source124.dtor_value;
            {
              RAST._IExpr _out845;
              DCOMP._IOwnership _out846;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out847;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out845, out _out846, out _out847);
              r = _out845;
              resultingOwnership = _out846;
              readIdents = _out847;
            }
          } else if (_source124.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2660___mcc_h782 = _source124.dtor_args;
            DAST._IType _2661___mcc_h783 = _source124.dtor_result;
            {
              RAST._IExpr _out848;
              DCOMP._IOwnership _out849;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out848, out _out849, out _out850);
              r = _out848;
              resultingOwnership = _out849;
              readIdents = _out850;
            }
          } else if (_source124.is_Primitive) {
            DAST._IPrimitive _2662___mcc_h786 = _source124.dtor_Primitive_a0;
            {
              RAST._IExpr _out851;
              DCOMP._IOwnership _out852;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out853;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out851, out _out852, out _out853);
              r = _out851;
              resultingOwnership = _out852;
              readIdents = _out853;
            }
          } else if (_source124.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2663___mcc_h788 = _source124.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2664___mcc_h790 = _source124.dtor_TypeArg_a0;
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
        } else if (_source98.is_Primitive) {
          DAST._IPrimitive _2665___mcc_h792 = _source98.dtor_Primitive_a0;
          DAST._IPrimitive _source126 = _2665___mcc_h792;
          if (_source126.is_Int) {
            DAST._IType _source127 = _2239___mcc_h1;
            if (_source127.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2666___mcc_h796 = _source127.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2667___mcc_h797 = _source127.dtor_typeArgs;
              DAST._IResolvedType _2668___mcc_h798 = _source127.dtor_resolved;
              DAST._IResolvedType _source128 = _2668___mcc_h798;
              if (_source128.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2669___mcc_h802 = _source128.dtor_path;
                {
                  RAST._IExpr _out860;
                  DCOMP._IOwnership _out861;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out860, out _out861, out _out862);
                  r = _out860;
                  resultingOwnership = _out861;
                  readIdents = _out862;
                }
              } else if (_source128.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2670___mcc_h804 = _source128.dtor_path;
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
                DAST._IType _2671___mcc_h806 = _source128.dtor_baseType;
                DAST._INewtypeRange _2672___mcc_h807 = _source128.dtor_range;
                bool _2673___mcc_h808 = _source128.dtor_erase;
                bool _2674_erase = _2673___mcc_h808;
                DAST._INewtypeRange _2675_range = _2672___mcc_h807;
                DAST._IType _2676_b = _2671___mcc_h806;
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
            } else if (_source127.is_Nullable) {
              DAST._IType _2677___mcc_h812 = _source127.dtor_Nullable_a0;
              {
                RAST._IExpr _out869;
                DCOMP._IOwnership _out870;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out871;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out869, out _out870, out _out871);
                r = _out869;
                resultingOwnership = _out870;
                readIdents = _out871;
              }
            } else if (_source127.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2678___mcc_h814 = _source127.dtor_Tuple_a0;
              {
                RAST._IExpr _out872;
                DCOMP._IOwnership _out873;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out872, out _out873, out _out874);
                r = _out872;
                resultingOwnership = _out873;
                readIdents = _out874;
              }
            } else if (_source127.is_Array) {
              DAST._IType _2679___mcc_h816 = _source127.dtor_element;
              BigInteger _2680___mcc_h817 = _source127.dtor_dims;
              {
                RAST._IExpr _out875;
                DCOMP._IOwnership _out876;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out877;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out875, out _out876, out _out877);
                r = _out875;
                resultingOwnership = _out876;
                readIdents = _out877;
              }
            } else if (_source127.is_Seq) {
              DAST._IType _2681___mcc_h820 = _source127.dtor_element;
              {
                RAST._IExpr _out878;
                DCOMP._IOwnership _out879;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out880;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out878, out _out879, out _out880);
                r = _out878;
                resultingOwnership = _out879;
                readIdents = _out880;
              }
            } else if (_source127.is_Set) {
              DAST._IType _2682___mcc_h822 = _source127.dtor_element;
              {
                RAST._IExpr _out881;
                DCOMP._IOwnership _out882;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out881, out _out882, out _out883);
                r = _out881;
                resultingOwnership = _out882;
                readIdents = _out883;
              }
            } else if (_source127.is_Multiset) {
              DAST._IType _2683___mcc_h824 = _source127.dtor_element;
              {
                RAST._IExpr _out884;
                DCOMP._IOwnership _out885;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out886;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out884, out _out885, out _out886);
                r = _out884;
                resultingOwnership = _out885;
                readIdents = _out886;
              }
            } else if (_source127.is_Map) {
              DAST._IType _2684___mcc_h826 = _source127.dtor_key;
              DAST._IType _2685___mcc_h827 = _source127.dtor_value;
              {
                RAST._IExpr _out887;
                DCOMP._IOwnership _out888;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out889;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out887, out _out888, out _out889);
                r = _out887;
                resultingOwnership = _out888;
                readIdents = _out889;
              }
            } else if (_source127.is_SetBuilder) {
              DAST._IType _2686___mcc_h830 = _source127.dtor_element;
              {
                RAST._IExpr _out890;
                DCOMP._IOwnership _out891;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out892;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out890, out _out891, out _out892);
                r = _out890;
                resultingOwnership = _out891;
                readIdents = _out892;
              }
            } else if (_source127.is_MapBuilder) {
              DAST._IType _2687___mcc_h832 = _source127.dtor_key;
              DAST._IType _2688___mcc_h833 = _source127.dtor_value;
              {
                RAST._IExpr _out893;
                DCOMP._IOwnership _out894;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out893, out _out894, out _out895);
                r = _out893;
                resultingOwnership = _out894;
                readIdents = _out895;
              }
            } else if (_source127.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2689___mcc_h836 = _source127.dtor_args;
              DAST._IType _2690___mcc_h837 = _source127.dtor_result;
              {
                RAST._IExpr _out896;
                DCOMP._IOwnership _out897;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out898;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out896, out _out897, out _out898);
                r = _out896;
                resultingOwnership = _out897;
                readIdents = _out898;
              }
            } else if (_source127.is_Primitive) {
              DAST._IPrimitive _2691___mcc_h840 = _source127.dtor_Primitive_a0;
              DAST._IPrimitive _source129 = _2691___mcc_h840;
              if (_source129.is_Int) {
                {
                  RAST._IExpr _out899;
                  DCOMP._IOwnership _out900;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out901;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out899, out _out900, out _out901);
                  r = _out899;
                  resultingOwnership = _out900;
                  readIdents = _out901;
                }
              } else if (_source129.is_Real) {
                {
                  RAST._IExpr _2692_recursiveGen;
                  DCOMP._IOwnership _2693___v71;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2694_recIdents;
                  RAST._IExpr _out902;
                  DCOMP._IOwnership _out903;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out904;
                  (this).GenExpr(_2232_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out902, out _out903, out _out904);
                  _2692_recursiveGen = _out902;
                  _2693___v71 = _out903;
                  _2694_recIdents = _out904;
                  r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_2692_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                  RAST._IExpr _out905;
                  DCOMP._IOwnership _out906;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out905, out _out906);
                  r = _out905;
                  resultingOwnership = _out906;
                  readIdents = _2694_recIdents;
                }
              } else if (_source129.is_String) {
                {
                  RAST._IExpr _out907;
                  DCOMP._IOwnership _out908;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out909;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out907, out _out908, out _out909);
                  r = _out907;
                  resultingOwnership = _out908;
                  readIdents = _out909;
                }
              } else if (_source129.is_Bool) {
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
                  RAST._IType _2695_rhsType;
                  RAST._IType _out913;
                  _out913 = (this).GenType(_2234_toTpe, true, false);
                  _2695_rhsType = _out913;
                  RAST._IExpr _2696_recursiveGen;
                  DCOMP._IOwnership _2697___v77;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2698_recIdents;
                  RAST._IExpr _out914;
                  DCOMP._IOwnership _out915;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out916;
                  (this).GenExpr(_2232_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out914, out _out915, out _out916);
                  _2696_recursiveGen = _out914;
                  _2697___v77 = _out915;
                  _2698_recIdents = _out916;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_2696_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                  RAST._IExpr _out917;
                  DCOMP._IOwnership _out918;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out917, out _out918);
                  r = _out917;
                  resultingOwnership = _out918;
                  readIdents = _2698_recIdents;
                }
              }
            } else if (_source127.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2699___mcc_h842 = _source127.dtor_Passthrough_a0;
              {
                RAST._IType _2700_rhsType;
                RAST._IType _out919;
                _out919 = (this).GenType(_2234_toTpe, true, false);
                _2700_rhsType = _out919;
                RAST._IExpr _2701_recursiveGen;
                DCOMP._IOwnership _2702___v74;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2703_recIdents;
                RAST._IExpr _out920;
                DCOMP._IOwnership _out921;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out922;
                (this).GenExpr(_2232_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out920, out _out921, out _out922);
                _2701_recursiveGen = _out920;
                _2702___v74 = _out921;
                _2703_recIdents = _out922;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_2700_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_2701_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                RAST._IExpr _out923;
                DCOMP._IOwnership _out924;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out923, out _out924);
                r = _out923;
                resultingOwnership = _out924;
                readIdents = _2703_recIdents;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2704___mcc_h844 = _source127.dtor_TypeArg_a0;
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
          } else if (_source126.is_Real) {
            DAST._IType _source130 = _2239___mcc_h1;
            if (_source130.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2705___mcc_h846 = _source130.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2706___mcc_h847 = _source130.dtor_typeArgs;
              DAST._IResolvedType _2707___mcc_h848 = _source130.dtor_resolved;
              DAST._IResolvedType _source131 = _2707___mcc_h848;
              if (_source131.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2708___mcc_h852 = _source131.dtor_path;
                {
                  RAST._IExpr _out928;
                  DCOMP._IOwnership _out929;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out930;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out928, out _out929, out _out930);
                  r = _out928;
                  resultingOwnership = _out929;
                  readIdents = _out930;
                }
              } else if (_source131.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2709___mcc_h854 = _source131.dtor_path;
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
                DAST._IType _2710___mcc_h856 = _source131.dtor_baseType;
                DAST._INewtypeRange _2711___mcc_h857 = _source131.dtor_range;
                bool _2712___mcc_h858 = _source131.dtor_erase;
                bool _2713_erase = _2712___mcc_h858;
                DAST._INewtypeRange _2714_range = _2711___mcc_h857;
                DAST._IType _2715_b = _2710___mcc_h856;
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
            } else if (_source130.is_Nullable) {
              DAST._IType _2716___mcc_h862 = _source130.dtor_Nullable_a0;
              {
                RAST._IExpr _out937;
                DCOMP._IOwnership _out938;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out939;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out937, out _out938, out _out939);
                r = _out937;
                resultingOwnership = _out938;
                readIdents = _out939;
              }
            } else if (_source130.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2717___mcc_h864 = _source130.dtor_Tuple_a0;
              {
                RAST._IExpr _out940;
                DCOMP._IOwnership _out941;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out942;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out940, out _out941, out _out942);
                r = _out940;
                resultingOwnership = _out941;
                readIdents = _out942;
              }
            } else if (_source130.is_Array) {
              DAST._IType _2718___mcc_h866 = _source130.dtor_element;
              BigInteger _2719___mcc_h867 = _source130.dtor_dims;
              {
                RAST._IExpr _out943;
                DCOMP._IOwnership _out944;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out945;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out943, out _out944, out _out945);
                r = _out943;
                resultingOwnership = _out944;
                readIdents = _out945;
              }
            } else if (_source130.is_Seq) {
              DAST._IType _2720___mcc_h870 = _source130.dtor_element;
              {
                RAST._IExpr _out946;
                DCOMP._IOwnership _out947;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out948;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out946, out _out947, out _out948);
                r = _out946;
                resultingOwnership = _out947;
                readIdents = _out948;
              }
            } else if (_source130.is_Set) {
              DAST._IType _2721___mcc_h872 = _source130.dtor_element;
              {
                RAST._IExpr _out949;
                DCOMP._IOwnership _out950;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out951;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out949, out _out950, out _out951);
                r = _out949;
                resultingOwnership = _out950;
                readIdents = _out951;
              }
            } else if (_source130.is_Multiset) {
              DAST._IType _2722___mcc_h874 = _source130.dtor_element;
              {
                RAST._IExpr _out952;
                DCOMP._IOwnership _out953;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out954;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out952, out _out953, out _out954);
                r = _out952;
                resultingOwnership = _out953;
                readIdents = _out954;
              }
            } else if (_source130.is_Map) {
              DAST._IType _2723___mcc_h876 = _source130.dtor_key;
              DAST._IType _2724___mcc_h877 = _source130.dtor_value;
              {
                RAST._IExpr _out955;
                DCOMP._IOwnership _out956;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out957;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out955, out _out956, out _out957);
                r = _out955;
                resultingOwnership = _out956;
                readIdents = _out957;
              }
            } else if (_source130.is_SetBuilder) {
              DAST._IType _2725___mcc_h880 = _source130.dtor_element;
              {
                RAST._IExpr _out958;
                DCOMP._IOwnership _out959;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out960;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out958, out _out959, out _out960);
                r = _out958;
                resultingOwnership = _out959;
                readIdents = _out960;
              }
            } else if (_source130.is_MapBuilder) {
              DAST._IType _2726___mcc_h882 = _source130.dtor_key;
              DAST._IType _2727___mcc_h883 = _source130.dtor_value;
              {
                RAST._IExpr _out961;
                DCOMP._IOwnership _out962;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out963;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out961, out _out962, out _out963);
                r = _out961;
                resultingOwnership = _out962;
                readIdents = _out963;
              }
            } else if (_source130.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2728___mcc_h886 = _source130.dtor_args;
              DAST._IType _2729___mcc_h887 = _source130.dtor_result;
              {
                RAST._IExpr _out964;
                DCOMP._IOwnership _out965;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out964, out _out965, out _out966);
                r = _out964;
                resultingOwnership = _out965;
                readIdents = _out966;
              }
            } else if (_source130.is_Primitive) {
              DAST._IPrimitive _2730___mcc_h890 = _source130.dtor_Primitive_a0;
              DAST._IPrimitive _source132 = _2730___mcc_h890;
              if (_source132.is_Int) {
                {
                  RAST._IExpr _2731_recursiveGen;
                  DCOMP._IOwnership _2732___v72;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2733_recIdents;
                  RAST._IExpr _out967;
                  DCOMP._IOwnership _out968;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out969;
                  (this).GenExpr(_2232_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out967, out _out968, out _out969);
                  _2731_recursiveGen = _out967;
                  _2732___v72 = _out968;
                  _2733_recIdents = _out969;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_2731_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                  RAST._IExpr _out970;
                  DCOMP._IOwnership _out971;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out970, out _out971);
                  r = _out970;
                  resultingOwnership = _out971;
                  readIdents = _2733_recIdents;
                }
              } else if (_source132.is_Real) {
                {
                  RAST._IExpr _out972;
                  DCOMP._IOwnership _out973;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out972, out _out973, out _out974);
                  r = _out972;
                  resultingOwnership = _out973;
                  readIdents = _out974;
                }
              } else if (_source132.is_String) {
                {
                  RAST._IExpr _out975;
                  DCOMP._IOwnership _out976;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out977;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out975, out _out976, out _out977);
                  r = _out975;
                  resultingOwnership = _out976;
                  readIdents = _out977;
                }
              } else if (_source132.is_Bool) {
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
            } else if (_source130.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2734___mcc_h892 = _source130.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _2735___mcc_h894 = _source130.dtor_TypeArg_a0;
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
          } else if (_source126.is_String) {
            DAST._IType _source133 = _2239___mcc_h1;
            if (_source133.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2736___mcc_h896 = _source133.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2737___mcc_h897 = _source133.dtor_typeArgs;
              DAST._IResolvedType _2738___mcc_h898 = _source133.dtor_resolved;
              DAST._IResolvedType _source134 = _2738___mcc_h898;
              if (_source134.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2739___mcc_h902 = _source134.dtor_path;
                {
                  RAST._IExpr _out990;
                  DCOMP._IOwnership _out991;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out992;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out990, out _out991, out _out992);
                  r = _out990;
                  resultingOwnership = _out991;
                  readIdents = _out992;
                }
              } else if (_source134.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2740___mcc_h904 = _source134.dtor_path;
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
                DAST._IType _2741___mcc_h906 = _source134.dtor_baseType;
                DAST._INewtypeRange _2742___mcc_h907 = _source134.dtor_range;
                bool _2743___mcc_h908 = _source134.dtor_erase;
                bool _2744_erase = _2743___mcc_h908;
                DAST._INewtypeRange _2745_range = _2742___mcc_h907;
                DAST._IType _2746_b = _2741___mcc_h906;
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
            } else if (_source133.is_Nullable) {
              DAST._IType _2747___mcc_h912 = _source133.dtor_Nullable_a0;
              {
                RAST._IExpr _out999;
                DCOMP._IOwnership _out1000;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1001;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out999, out _out1000, out _out1001);
                r = _out999;
                resultingOwnership = _out1000;
                readIdents = _out1001;
              }
            } else if (_source133.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2748___mcc_h914 = _source133.dtor_Tuple_a0;
              {
                RAST._IExpr _out1002;
                DCOMP._IOwnership _out1003;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1004;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1002, out _out1003, out _out1004);
                r = _out1002;
                resultingOwnership = _out1003;
                readIdents = _out1004;
              }
            } else if (_source133.is_Array) {
              DAST._IType _2749___mcc_h916 = _source133.dtor_element;
              BigInteger _2750___mcc_h917 = _source133.dtor_dims;
              {
                RAST._IExpr _out1005;
                DCOMP._IOwnership _out1006;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1007;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1005, out _out1006, out _out1007);
                r = _out1005;
                resultingOwnership = _out1006;
                readIdents = _out1007;
              }
            } else if (_source133.is_Seq) {
              DAST._IType _2751___mcc_h920 = _source133.dtor_element;
              {
                RAST._IExpr _out1008;
                DCOMP._IOwnership _out1009;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1010;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1008, out _out1009, out _out1010);
                r = _out1008;
                resultingOwnership = _out1009;
                readIdents = _out1010;
              }
            } else if (_source133.is_Set) {
              DAST._IType _2752___mcc_h922 = _source133.dtor_element;
              {
                RAST._IExpr _out1011;
                DCOMP._IOwnership _out1012;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1013;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1011, out _out1012, out _out1013);
                r = _out1011;
                resultingOwnership = _out1012;
                readIdents = _out1013;
              }
            } else if (_source133.is_Multiset) {
              DAST._IType _2753___mcc_h924 = _source133.dtor_element;
              {
                RAST._IExpr _out1014;
                DCOMP._IOwnership _out1015;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1016;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1014, out _out1015, out _out1016);
                r = _out1014;
                resultingOwnership = _out1015;
                readIdents = _out1016;
              }
            } else if (_source133.is_Map) {
              DAST._IType _2754___mcc_h926 = _source133.dtor_key;
              DAST._IType _2755___mcc_h927 = _source133.dtor_value;
              {
                RAST._IExpr _out1017;
                DCOMP._IOwnership _out1018;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1019;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1017, out _out1018, out _out1019);
                r = _out1017;
                resultingOwnership = _out1018;
                readIdents = _out1019;
              }
            } else if (_source133.is_SetBuilder) {
              DAST._IType _2756___mcc_h930 = _source133.dtor_element;
              {
                RAST._IExpr _out1020;
                DCOMP._IOwnership _out1021;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1022;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1020, out _out1021, out _out1022);
                r = _out1020;
                resultingOwnership = _out1021;
                readIdents = _out1022;
              }
            } else if (_source133.is_MapBuilder) {
              DAST._IType _2757___mcc_h932 = _source133.dtor_key;
              DAST._IType _2758___mcc_h933 = _source133.dtor_value;
              {
                RAST._IExpr _out1023;
                DCOMP._IOwnership _out1024;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1025;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1023, out _out1024, out _out1025);
                r = _out1023;
                resultingOwnership = _out1024;
                readIdents = _out1025;
              }
            } else if (_source133.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2759___mcc_h936 = _source133.dtor_args;
              DAST._IType _2760___mcc_h937 = _source133.dtor_result;
              {
                RAST._IExpr _out1026;
                DCOMP._IOwnership _out1027;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1028;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1026, out _out1027, out _out1028);
                r = _out1026;
                resultingOwnership = _out1027;
                readIdents = _out1028;
              }
            } else if (_source133.is_Primitive) {
              DAST._IPrimitive _2761___mcc_h940 = _source133.dtor_Primitive_a0;
              {
                RAST._IExpr _out1029;
                DCOMP._IOwnership _out1030;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1031;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1029, out _out1030, out _out1031);
                r = _out1029;
                resultingOwnership = _out1030;
                readIdents = _out1031;
              }
            } else if (_source133.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2762___mcc_h942 = _source133.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _2763___mcc_h944 = _source133.dtor_TypeArg_a0;
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
          } else if (_source126.is_Bool) {
            DAST._IType _source135 = _2239___mcc_h1;
            if (_source135.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2764___mcc_h946 = _source135.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2765___mcc_h947 = _source135.dtor_typeArgs;
              DAST._IResolvedType _2766___mcc_h948 = _source135.dtor_resolved;
              DAST._IResolvedType _source136 = _2766___mcc_h948;
              if (_source136.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2767___mcc_h952 = _source136.dtor_path;
                {
                  RAST._IExpr _out1038;
                  DCOMP._IOwnership _out1039;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1040;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1038, out _out1039, out _out1040);
                  r = _out1038;
                  resultingOwnership = _out1039;
                  readIdents = _out1040;
                }
              } else if (_source136.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2768___mcc_h954 = _source136.dtor_path;
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
                DAST._IType _2769___mcc_h956 = _source136.dtor_baseType;
                DAST._INewtypeRange _2770___mcc_h957 = _source136.dtor_range;
                bool _2771___mcc_h958 = _source136.dtor_erase;
                bool _2772_erase = _2771___mcc_h958;
                DAST._INewtypeRange _2773_range = _2770___mcc_h957;
                DAST._IType _2774_b = _2769___mcc_h956;
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
            } else if (_source135.is_Nullable) {
              DAST._IType _2775___mcc_h962 = _source135.dtor_Nullable_a0;
              {
                RAST._IExpr _out1047;
                DCOMP._IOwnership _out1048;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1049;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1047, out _out1048, out _out1049);
                r = _out1047;
                resultingOwnership = _out1048;
                readIdents = _out1049;
              }
            } else if (_source135.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2776___mcc_h964 = _source135.dtor_Tuple_a0;
              {
                RAST._IExpr _out1050;
                DCOMP._IOwnership _out1051;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1052;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1050, out _out1051, out _out1052);
                r = _out1050;
                resultingOwnership = _out1051;
                readIdents = _out1052;
              }
            } else if (_source135.is_Array) {
              DAST._IType _2777___mcc_h966 = _source135.dtor_element;
              BigInteger _2778___mcc_h967 = _source135.dtor_dims;
              {
                RAST._IExpr _out1053;
                DCOMP._IOwnership _out1054;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1053, out _out1054, out _out1055);
                r = _out1053;
                resultingOwnership = _out1054;
                readIdents = _out1055;
              }
            } else if (_source135.is_Seq) {
              DAST._IType _2779___mcc_h970 = _source135.dtor_element;
              {
                RAST._IExpr _out1056;
                DCOMP._IOwnership _out1057;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1058;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1056, out _out1057, out _out1058);
                r = _out1056;
                resultingOwnership = _out1057;
                readIdents = _out1058;
              }
            } else if (_source135.is_Set) {
              DAST._IType _2780___mcc_h972 = _source135.dtor_element;
              {
                RAST._IExpr _out1059;
                DCOMP._IOwnership _out1060;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1061;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1059, out _out1060, out _out1061);
                r = _out1059;
                resultingOwnership = _out1060;
                readIdents = _out1061;
              }
            } else if (_source135.is_Multiset) {
              DAST._IType _2781___mcc_h974 = _source135.dtor_element;
              {
                RAST._IExpr _out1062;
                DCOMP._IOwnership _out1063;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1064;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1062, out _out1063, out _out1064);
                r = _out1062;
                resultingOwnership = _out1063;
                readIdents = _out1064;
              }
            } else if (_source135.is_Map) {
              DAST._IType _2782___mcc_h976 = _source135.dtor_key;
              DAST._IType _2783___mcc_h977 = _source135.dtor_value;
              {
                RAST._IExpr _out1065;
                DCOMP._IOwnership _out1066;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1065, out _out1066, out _out1067);
                r = _out1065;
                resultingOwnership = _out1066;
                readIdents = _out1067;
              }
            } else if (_source135.is_SetBuilder) {
              DAST._IType _2784___mcc_h980 = _source135.dtor_element;
              {
                RAST._IExpr _out1068;
                DCOMP._IOwnership _out1069;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1070;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1068, out _out1069, out _out1070);
                r = _out1068;
                resultingOwnership = _out1069;
                readIdents = _out1070;
              }
            } else if (_source135.is_MapBuilder) {
              DAST._IType _2785___mcc_h982 = _source135.dtor_key;
              DAST._IType _2786___mcc_h983 = _source135.dtor_value;
              {
                RAST._IExpr _out1071;
                DCOMP._IOwnership _out1072;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1073;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1071, out _out1072, out _out1073);
                r = _out1071;
                resultingOwnership = _out1072;
                readIdents = _out1073;
              }
            } else if (_source135.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2787___mcc_h986 = _source135.dtor_args;
              DAST._IType _2788___mcc_h987 = _source135.dtor_result;
              {
                RAST._IExpr _out1074;
                DCOMP._IOwnership _out1075;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1076;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1074, out _out1075, out _out1076);
                r = _out1074;
                resultingOwnership = _out1075;
                readIdents = _out1076;
              }
            } else if (_source135.is_Primitive) {
              DAST._IPrimitive _2789___mcc_h990 = _source135.dtor_Primitive_a0;
              {
                RAST._IExpr _out1077;
                DCOMP._IOwnership _out1078;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1077, out _out1078, out _out1079);
                r = _out1077;
                resultingOwnership = _out1078;
                readIdents = _out1079;
              }
            } else if (_source135.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2790___mcc_h992 = _source135.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _2791___mcc_h994 = _source135.dtor_TypeArg_a0;
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
            DAST._IType _source137 = _2239___mcc_h1;
            if (_source137.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2792___mcc_h996 = _source137.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _2793___mcc_h997 = _source137.dtor_typeArgs;
              DAST._IResolvedType _2794___mcc_h998 = _source137.dtor_resolved;
              DAST._IResolvedType _source138 = _2794___mcc_h998;
              if (_source138.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2795___mcc_h1002 = _source138.dtor_path;
                {
                  RAST._IExpr _out1086;
                  DCOMP._IOwnership _out1087;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1088;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1086, out _out1087, out _out1088);
                  r = _out1086;
                  resultingOwnership = _out1087;
                  readIdents = _out1088;
                }
              } else if (_source138.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2796___mcc_h1004 = _source138.dtor_path;
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
                DAST._IType _2797___mcc_h1006 = _source138.dtor_baseType;
                DAST._INewtypeRange _2798___mcc_h1007 = _source138.dtor_range;
                bool _2799___mcc_h1008 = _source138.dtor_erase;
                bool _2800_erase = _2799___mcc_h1008;
                DAST._INewtypeRange _2801_range = _2798___mcc_h1007;
                DAST._IType _2802_b = _2797___mcc_h1006;
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
            } else if (_source137.is_Nullable) {
              DAST._IType _2803___mcc_h1012 = _source137.dtor_Nullable_a0;
              {
                RAST._IExpr _out1095;
                DCOMP._IOwnership _out1096;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1097;
                (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1095, out _out1096, out _out1097);
                r = _out1095;
                resultingOwnership = _out1096;
                readIdents = _out1097;
              }
            } else if (_source137.is_Tuple) {
              Dafny.ISequence<DAST._IType> _2804___mcc_h1014 = _source137.dtor_Tuple_a0;
              {
                RAST._IExpr _out1098;
                DCOMP._IOwnership _out1099;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1098, out _out1099, out _out1100);
                r = _out1098;
                resultingOwnership = _out1099;
                readIdents = _out1100;
              }
            } else if (_source137.is_Array) {
              DAST._IType _2805___mcc_h1016 = _source137.dtor_element;
              BigInteger _2806___mcc_h1017 = _source137.dtor_dims;
              {
                RAST._IExpr _out1101;
                DCOMP._IOwnership _out1102;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1103;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1101, out _out1102, out _out1103);
                r = _out1101;
                resultingOwnership = _out1102;
                readIdents = _out1103;
              }
            } else if (_source137.is_Seq) {
              DAST._IType _2807___mcc_h1020 = _source137.dtor_element;
              {
                RAST._IExpr _out1104;
                DCOMP._IOwnership _out1105;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1106;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1104, out _out1105, out _out1106);
                r = _out1104;
                resultingOwnership = _out1105;
                readIdents = _out1106;
              }
            } else if (_source137.is_Set) {
              DAST._IType _2808___mcc_h1022 = _source137.dtor_element;
              {
                RAST._IExpr _out1107;
                DCOMP._IOwnership _out1108;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1109;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1107, out _out1108, out _out1109);
                r = _out1107;
                resultingOwnership = _out1108;
                readIdents = _out1109;
              }
            } else if (_source137.is_Multiset) {
              DAST._IType _2809___mcc_h1024 = _source137.dtor_element;
              {
                RAST._IExpr _out1110;
                DCOMP._IOwnership _out1111;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1110, out _out1111, out _out1112);
                r = _out1110;
                resultingOwnership = _out1111;
                readIdents = _out1112;
              }
            } else if (_source137.is_Map) {
              DAST._IType _2810___mcc_h1026 = _source137.dtor_key;
              DAST._IType _2811___mcc_h1027 = _source137.dtor_value;
              {
                RAST._IExpr _out1113;
                DCOMP._IOwnership _out1114;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1115;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1113, out _out1114, out _out1115);
                r = _out1113;
                resultingOwnership = _out1114;
                readIdents = _out1115;
              }
            } else if (_source137.is_SetBuilder) {
              DAST._IType _2812___mcc_h1030 = _source137.dtor_element;
              {
                RAST._IExpr _out1116;
                DCOMP._IOwnership _out1117;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1118;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1116, out _out1117, out _out1118);
                r = _out1116;
                resultingOwnership = _out1117;
                readIdents = _out1118;
              }
            } else if (_source137.is_MapBuilder) {
              DAST._IType _2813___mcc_h1032 = _source137.dtor_key;
              DAST._IType _2814___mcc_h1033 = _source137.dtor_value;
              {
                RAST._IExpr _out1119;
                DCOMP._IOwnership _out1120;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1121;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1119, out _out1120, out _out1121);
                r = _out1119;
                resultingOwnership = _out1120;
                readIdents = _out1121;
              }
            } else if (_source137.is_Arrow) {
              Dafny.ISequence<DAST._IType> _2815___mcc_h1036 = _source137.dtor_args;
              DAST._IType _2816___mcc_h1037 = _source137.dtor_result;
              {
                RAST._IExpr _out1122;
                DCOMP._IOwnership _out1123;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1122, out _out1123, out _out1124);
                r = _out1122;
                resultingOwnership = _out1123;
                readIdents = _out1124;
              }
            } else if (_source137.is_Primitive) {
              DAST._IPrimitive _2817___mcc_h1040 = _source137.dtor_Primitive_a0;
              DAST._IPrimitive _source139 = _2817___mcc_h1040;
              if (_source139.is_Int) {
                {
                  RAST._IType _2818_rhsType;
                  RAST._IType _out1125;
                  _out1125 = (this).GenType(_2233_fromTpe, true, false);
                  _2818_rhsType = _out1125;
                  RAST._IExpr _2819_recursiveGen;
                  DCOMP._IOwnership _2820___v78;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2821_recIdents;
                  RAST._IExpr _out1126;
                  DCOMP._IOwnership _out1127;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1128;
                  (this).GenExpr(_2232_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1126, out _out1127, out _out1128);
                  _2819_recursiveGen = _out1126;
                  _2820___v78 = _out1127;
                  _2821_recIdents = _out1128;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::BigInt::from("), (_2819_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)}")));
                  RAST._IExpr _out1129;
                  DCOMP._IOwnership _out1130;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1129, out _out1130);
                  r = _out1129;
                  resultingOwnership = _out1130;
                  readIdents = _2821_recIdents;
                }
              } else if (_source139.is_Real) {
                {
                  RAST._IExpr _out1131;
                  DCOMP._IOwnership _out1132;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1133;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1131, out _out1132, out _out1133);
                  r = _out1131;
                  resultingOwnership = _out1132;
                  readIdents = _out1133;
                }
              } else if (_source139.is_String) {
                {
                  RAST._IExpr _out1134;
                  DCOMP._IOwnership _out1135;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                  (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1134, out _out1135, out _out1136);
                  r = _out1134;
                  resultingOwnership = _out1135;
                  readIdents = _out1136;
                }
              } else if (_source139.is_Bool) {
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
            } else if (_source137.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _2822___mcc_h1042 = _source137.dtor_Passthrough_a0;
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
              Dafny.ISequence<Dafny.Rune> _2823___mcc_h1044 = _source137.dtor_TypeArg_a0;
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
        } else if (_source98.is_Passthrough) {
          Dafny.ISequence<Dafny.Rune> _2824___mcc_h1046 = _source98.dtor_Passthrough_a0;
          DAST._IType _source140 = _2239___mcc_h1;
          if (_source140.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2825___mcc_h1050 = _source140.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2826___mcc_h1051 = _source140.dtor_typeArgs;
            DAST._IResolvedType _2827___mcc_h1052 = _source140.dtor_resolved;
            DAST._IResolvedType _source141 = _2827___mcc_h1052;
            if (_source141.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2828___mcc_h1056 = _source141.dtor_path;
              {
                RAST._IExpr _out1149;
                DCOMP._IOwnership _out1150;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1151;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1149, out _out1150, out _out1151);
                r = _out1149;
                resultingOwnership = _out1150;
                readIdents = _out1151;
              }
            } else if (_source141.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2829___mcc_h1058 = _source141.dtor_path;
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
              DAST._IType _2830___mcc_h1060 = _source141.dtor_baseType;
              DAST._INewtypeRange _2831___mcc_h1061 = _source141.dtor_range;
              bool _2832___mcc_h1062 = _source141.dtor_erase;
              bool _2833_erase = _2832___mcc_h1062;
              DAST._INewtypeRange _2834_range = _2831___mcc_h1061;
              DAST._IType _2835_b = _2830___mcc_h1060;
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
          } else if (_source140.is_Nullable) {
            DAST._IType _2836___mcc_h1066 = _source140.dtor_Nullable_a0;
            {
              RAST._IExpr _out1158;
              DCOMP._IOwnership _out1159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1160;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1158, out _out1159, out _out1160);
              r = _out1158;
              resultingOwnership = _out1159;
              readIdents = _out1160;
            }
          } else if (_source140.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2837___mcc_h1068 = _source140.dtor_Tuple_a0;
            {
              RAST._IExpr _out1161;
              DCOMP._IOwnership _out1162;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1163;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1161, out _out1162, out _out1163);
              r = _out1161;
              resultingOwnership = _out1162;
              readIdents = _out1163;
            }
          } else if (_source140.is_Array) {
            DAST._IType _2838___mcc_h1070 = _source140.dtor_element;
            BigInteger _2839___mcc_h1071 = _source140.dtor_dims;
            {
              RAST._IExpr _out1164;
              DCOMP._IOwnership _out1165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1166;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1164, out _out1165, out _out1166);
              r = _out1164;
              resultingOwnership = _out1165;
              readIdents = _out1166;
            }
          } else if (_source140.is_Seq) {
            DAST._IType _2840___mcc_h1074 = _source140.dtor_element;
            {
              RAST._IExpr _out1167;
              DCOMP._IOwnership _out1168;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1167, out _out1168, out _out1169);
              r = _out1167;
              resultingOwnership = _out1168;
              readIdents = _out1169;
            }
          } else if (_source140.is_Set) {
            DAST._IType _2841___mcc_h1076 = _source140.dtor_element;
            {
              RAST._IExpr _out1170;
              DCOMP._IOwnership _out1171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1172;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1170, out _out1171, out _out1172);
              r = _out1170;
              resultingOwnership = _out1171;
              readIdents = _out1172;
            }
          } else if (_source140.is_Multiset) {
            DAST._IType _2842___mcc_h1078 = _source140.dtor_element;
            {
              RAST._IExpr _out1173;
              DCOMP._IOwnership _out1174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1175;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1173, out _out1174, out _out1175);
              r = _out1173;
              resultingOwnership = _out1174;
              readIdents = _out1175;
            }
          } else if (_source140.is_Map) {
            DAST._IType _2843___mcc_h1080 = _source140.dtor_key;
            DAST._IType _2844___mcc_h1081 = _source140.dtor_value;
            {
              RAST._IExpr _out1176;
              DCOMP._IOwnership _out1177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1178;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1176, out _out1177, out _out1178);
              r = _out1176;
              resultingOwnership = _out1177;
              readIdents = _out1178;
            }
          } else if (_source140.is_SetBuilder) {
            DAST._IType _2845___mcc_h1084 = _source140.dtor_element;
            {
              RAST._IExpr _out1179;
              DCOMP._IOwnership _out1180;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1179, out _out1180, out _out1181);
              r = _out1179;
              resultingOwnership = _out1180;
              readIdents = _out1181;
            }
          } else if (_source140.is_MapBuilder) {
            DAST._IType _2846___mcc_h1086 = _source140.dtor_key;
            DAST._IType _2847___mcc_h1087 = _source140.dtor_value;
            {
              RAST._IExpr _out1182;
              DCOMP._IOwnership _out1183;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1184;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1182, out _out1183, out _out1184);
              r = _out1182;
              resultingOwnership = _out1183;
              readIdents = _out1184;
            }
          } else if (_source140.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2848___mcc_h1090 = _source140.dtor_args;
            DAST._IType _2849___mcc_h1091 = _source140.dtor_result;
            {
              RAST._IExpr _out1185;
              DCOMP._IOwnership _out1186;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1187;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1185, out _out1186, out _out1187);
              r = _out1185;
              resultingOwnership = _out1186;
              readIdents = _out1187;
            }
          } else if (_source140.is_Primitive) {
            DAST._IPrimitive _2850___mcc_h1094 = _source140.dtor_Primitive_a0;
            DAST._IPrimitive _source142 = _2850___mcc_h1094;
            if (_source142.is_Int) {
              {
                RAST._IType _2851_rhsType;
                RAST._IType _out1188;
                _out1188 = (this).GenType(_2233_fromTpe, true, false);
                _2851_rhsType = _out1188;
                RAST._IExpr _2852_recursiveGen;
                DCOMP._IOwnership _2853___v76;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2854_recIdents;
                RAST._IExpr _out1189;
                DCOMP._IOwnership _out1190;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1191;
                (this).GenExpr(_2232_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1189, out _out1190, out _out1191);
                _2852_recursiveGen = _out1189;
                _2853___v76 = _out1190;
                _2854_recIdents = _out1191;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_2852_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                RAST._IExpr _out1192;
                DCOMP._IOwnership _out1193;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1192, out _out1193);
                r = _out1192;
                resultingOwnership = _out1193;
                readIdents = _2854_recIdents;
              }
            } else if (_source142.is_Real) {
              {
                RAST._IExpr _out1194;
                DCOMP._IOwnership _out1195;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1196;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1194, out _out1195, out _out1196);
                r = _out1194;
                resultingOwnership = _out1195;
                readIdents = _out1196;
              }
            } else if (_source142.is_String) {
              {
                RAST._IExpr _out1197;
                DCOMP._IOwnership _out1198;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1199;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1197, out _out1198, out _out1199);
                r = _out1197;
                resultingOwnership = _out1198;
                readIdents = _out1199;
              }
            } else if (_source142.is_Bool) {
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
          } else if (_source140.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2855___mcc_h1096 = _source140.dtor_Passthrough_a0;
            {
              RAST._IExpr _2856_recursiveGen;
              DCOMP._IOwnership _2857___v81;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2858_recIdents;
              RAST._IExpr _out1206;
              DCOMP._IOwnership _out1207;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1208;
              (this).GenExpr(_2232_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1206, out _out1207, out _out1208);
              _2856_recursiveGen = _out1206;
              _2857___v81 = _out1207;
              _2858_recIdents = _out1208;
              RAST._IType _2859_toTpeGen;
              RAST._IType _out1209;
              _out1209 = (this).GenType(_2234_toTpe, true, false);
              _2859_toTpeGen = _out1209;
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_2856_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_2859_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
              RAST._IExpr _out1210;
              DCOMP._IOwnership _out1211;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1210, out _out1211);
              r = _out1210;
              resultingOwnership = _out1211;
              readIdents = _2858_recIdents;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2860___mcc_h1098 = _source140.dtor_TypeArg_a0;
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
          Dafny.ISequence<Dafny.Rune> _2861___mcc_h1100 = _source98.dtor_TypeArg_a0;
          DAST._IType _source143 = _2239___mcc_h1;
          if (_source143.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2862___mcc_h1104 = _source143.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _2863___mcc_h1105 = _source143.dtor_typeArgs;
            DAST._IResolvedType _2864___mcc_h1106 = _source143.dtor_resolved;
            DAST._IResolvedType _source144 = _2864___mcc_h1106;
            if (_source144.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2865___mcc_h1110 = _source144.dtor_path;
              {
                RAST._IExpr _out1215;
                DCOMP._IOwnership _out1216;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1217;
                (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1215, out _out1216, out _out1217);
                r = _out1215;
                resultingOwnership = _out1216;
                readIdents = _out1217;
              }
            } else if (_source144.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2866___mcc_h1112 = _source144.dtor_path;
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
              DAST._IType _2867___mcc_h1114 = _source144.dtor_baseType;
              DAST._INewtypeRange _2868___mcc_h1115 = _source144.dtor_range;
              bool _2869___mcc_h1116 = _source144.dtor_erase;
              bool _2870_erase = _2869___mcc_h1116;
              DAST._INewtypeRange _2871_range = _2868___mcc_h1115;
              DAST._IType _2872_b = _2867___mcc_h1114;
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
          } else if (_source143.is_Nullable) {
            DAST._IType _2873___mcc_h1120 = _source143.dtor_Nullable_a0;
            {
              RAST._IExpr _out1224;
              DCOMP._IOwnership _out1225;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out1224, out _out1225, out _out1226);
              r = _out1224;
              resultingOwnership = _out1225;
              readIdents = _out1226;
            }
          } else if (_source143.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2874___mcc_h1122 = _source143.dtor_Tuple_a0;
            {
              RAST._IExpr _out1227;
              DCOMP._IOwnership _out1228;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1229;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1227, out _out1228, out _out1229);
              r = _out1227;
              resultingOwnership = _out1228;
              readIdents = _out1229;
            }
          } else if (_source143.is_Array) {
            DAST._IType _2875___mcc_h1124 = _source143.dtor_element;
            BigInteger _2876___mcc_h1125 = _source143.dtor_dims;
            {
              RAST._IExpr _out1230;
              DCOMP._IOwnership _out1231;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1232;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1230, out _out1231, out _out1232);
              r = _out1230;
              resultingOwnership = _out1231;
              readIdents = _out1232;
            }
          } else if (_source143.is_Seq) {
            DAST._IType _2877___mcc_h1128 = _source143.dtor_element;
            {
              RAST._IExpr _out1233;
              DCOMP._IOwnership _out1234;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1235;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1233, out _out1234, out _out1235);
              r = _out1233;
              resultingOwnership = _out1234;
              readIdents = _out1235;
            }
          } else if (_source143.is_Set) {
            DAST._IType _2878___mcc_h1130 = _source143.dtor_element;
            {
              RAST._IExpr _out1236;
              DCOMP._IOwnership _out1237;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1238;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1236, out _out1237, out _out1238);
              r = _out1236;
              resultingOwnership = _out1237;
              readIdents = _out1238;
            }
          } else if (_source143.is_Multiset) {
            DAST._IType _2879___mcc_h1132 = _source143.dtor_element;
            {
              RAST._IExpr _out1239;
              DCOMP._IOwnership _out1240;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1241;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1239, out _out1240, out _out1241);
              r = _out1239;
              resultingOwnership = _out1240;
              readIdents = _out1241;
            }
          } else if (_source143.is_Map) {
            DAST._IType _2880___mcc_h1134 = _source143.dtor_key;
            DAST._IType _2881___mcc_h1135 = _source143.dtor_value;
            {
              RAST._IExpr _out1242;
              DCOMP._IOwnership _out1243;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1244;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1242, out _out1243, out _out1244);
              r = _out1242;
              resultingOwnership = _out1243;
              readIdents = _out1244;
            }
          } else if (_source143.is_SetBuilder) {
            DAST._IType _2882___mcc_h1138 = _source143.dtor_element;
            {
              RAST._IExpr _out1245;
              DCOMP._IOwnership _out1246;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1245, out _out1246, out _out1247);
              r = _out1245;
              resultingOwnership = _out1246;
              readIdents = _out1247;
            }
          } else if (_source143.is_MapBuilder) {
            DAST._IType _2883___mcc_h1140 = _source143.dtor_key;
            DAST._IType _2884___mcc_h1141 = _source143.dtor_value;
            {
              RAST._IExpr _out1248;
              DCOMP._IOwnership _out1249;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1250;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1248, out _out1249, out _out1250);
              r = _out1248;
              resultingOwnership = _out1249;
              readIdents = _out1250;
            }
          } else if (_source143.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2885___mcc_h1144 = _source143.dtor_args;
            DAST._IType _2886___mcc_h1145 = _source143.dtor_result;
            {
              RAST._IExpr _out1251;
              DCOMP._IOwnership _out1252;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1253;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1251, out _out1252, out _out1253);
              r = _out1251;
              resultingOwnership = _out1252;
              readIdents = _out1253;
            }
          } else if (_source143.is_Primitive) {
            DAST._IPrimitive _2887___mcc_h1148 = _source143.dtor_Primitive_a0;
            {
              RAST._IExpr _out1254;
              DCOMP._IOwnership _out1255;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1256;
              (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out1254, out _out1255, out _out1256);
              r = _out1254;
              resultingOwnership = _out1255;
              readIdents = _out1256;
            }
          } else if (_source143.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2888___mcc_h1150 = _source143.dtor_Passthrough_a0;
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
            Dafny.ISequence<Dafny.Rune> _2889___mcc_h1152 = _source143.dtor_TypeArg_a0;
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
      DAST._IExpression _source145 = e;
      if (_source145.is_Literal) {
        DAST._ILiteral _2890___mcc_h0 = _source145.dtor_Literal_a0;
        RAST._IExpr _out1263;
        DCOMP._IOwnership _out1264;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1265;
        (this).GenExprLiteral(e, selfIdent, @params, expectedOwnership, out _out1263, out _out1264, out _out1265);
        r = _out1263;
        resultingOwnership = _out1264;
        readIdents = _out1265;
      } else if (_source145.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _2891___mcc_h1 = _source145.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _2892_name = _2891___mcc_h1;
        {
          r = RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent(_2892_name));
          bool _2893_currentlyBorrowed;
          _2893_currentlyBorrowed = (@params).Contains(_2892_name);
          if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
            r = RAST.__default.BorrowMut(r);
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
          } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
            r = RAST.__default.Clone(r);
            resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          } else if (_2893_currentlyBorrowed) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          } else {
            r = RAST.__default.Borrow(r);
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2892_name);
          return ;
        }
      } else if (_source145.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2894___mcc_h2 = _source145.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2895_path = _2894___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _2896_p;
          Dafny.ISequence<Dafny.Rune> _out1266;
          _out1266 = DCOMP.COMP.GenPath(_2895_path);
          _2896_p = _out1266;
          r = RAST.Expr.create_RawExpr(_2896_p);
          RAST._IExpr _out1267;
          DCOMP._IOwnership _out1268;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1267, out _out1268);
          r = _out1267;
          resultingOwnership = _out1268;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source145.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _2897___mcc_h3 = _source145.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _2898_values = _2897___mcc_h3;
        {
          Dafny.ISequence<Dafny.Rune> _2899_s;
          _2899_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2900_i;
          _2900_i = BigInteger.Zero;
          while ((_2900_i) < (new BigInteger((_2898_values).Count))) {
            if ((_2900_i).Sign == 1) {
              _2899_s = Dafny.Sequence<Dafny.Rune>.Concat(_2899_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            RAST._IExpr _2901_recursiveGen;
            DCOMP._IOwnership _2902___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2903_recIdents;
            RAST._IExpr _out1269;
            DCOMP._IOwnership _out1270;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1271;
            (this).GenExpr((_2898_values).Select(_2900_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1269, out _out1270, out _out1271);
            _2901_recursiveGen = _out1269;
            _2902___v84 = _out1270;
            _2903_recIdents = _out1271;
            _2899_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2899_s, (_2901_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2903_recIdents);
            _2900_i = (_2900_i) + (BigInteger.One);
          }
          _2899_s = Dafny.Sequence<Dafny.Rune>.Concat(_2899_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          r = RAST.Expr.create_RawExpr(_2899_s);
          RAST._IExpr _out1272;
          DCOMP._IOwnership _out1273;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1272, out _out1273);
          r = _out1272;
          resultingOwnership = _out1273;
          return ;
        }
      } else if (_source145.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2904___mcc_h4 = _source145.dtor_path;
        Dafny.ISequence<DAST._IType> _2905___mcc_h5 = _source145.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2906___mcc_h6 = _source145.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2907_args = _2906___mcc_h6;
        Dafny.ISequence<DAST._IType> _2908_typeArgs = _2905___mcc_h5;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2909_path = _2904___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _2910_path;
          Dafny.ISequence<Dafny.Rune> _out1274;
          _out1274 = DCOMP.COMP.GenPath(_2909_path);
          _2910_path = _out1274;
          Dafny.ISequence<Dafny.Rune> _2911_s;
          _2911_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2910_path);
          if ((new BigInteger((_2908_typeArgs).Count)).Sign == 1) {
            BigInteger _2912_i;
            _2912_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IType> _2913_typeExprs;
            _2913_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            while ((_2912_i) < (new BigInteger((_2908_typeArgs).Count))) {
              RAST._IType _2914_typeExpr;
              RAST._IType _out1275;
              _out1275 = (this).GenType((_2908_typeArgs).Select(_2912_i), false, false);
              _2914_typeExpr = _out1275;
              _2913_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2913_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2914_typeExpr));
              _2912_i = (_2912_i) + (BigInteger.One);
            }
            _2911_s = Dafny.Sequence<Dafny.Rune>.Concat(_2911_s, (RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2913_typeExprs))._ToString(DCOMP.__default.IND));
          }
          _2911_s = Dafny.Sequence<Dafny.Rune>.Concat(_2911_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2915_i;
          _2915_i = BigInteger.Zero;
          while ((_2915_i) < (new BigInteger((_2907_args).Count))) {
            if ((_2915_i).Sign == 1) {
              _2911_s = Dafny.Sequence<Dafny.Rune>.Concat(_2911_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IExpr _2916_recursiveGen;
            DCOMP._IOwnership _2917___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2918_recIdents;
            RAST._IExpr _out1276;
            DCOMP._IOwnership _out1277;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1278;
            (this).GenExpr((_2907_args).Select(_2915_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1276, out _out1277, out _out1278);
            _2916_recursiveGen = _out1276;
            _2917___v85 = _out1277;
            _2918_recIdents = _out1278;
            _2911_s = Dafny.Sequence<Dafny.Rune>.Concat(_2911_s, (_2916_recursiveGen)._ToString(DCOMP.__default.IND));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2918_recIdents);
            _2915_i = (_2915_i) + (BigInteger.One);
          }
          _2911_s = Dafny.Sequence<Dafny.Rune>.Concat(_2911_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          r = RAST.Expr.create_RawExpr(_2911_s);
          RAST._IExpr _out1279;
          DCOMP._IOwnership _out1280;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1279, out _out1280);
          r = _out1279;
          resultingOwnership = _out1280;
          return ;
        }
      } else if (_source145.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _2919___mcc_h7 = _source145.dtor_dims;
        DAST._IType _2920___mcc_h8 = _source145.dtor_typ;
        DAST._IType _2921_typ = _2920___mcc_h8;
        Dafny.ISequence<DAST._IExpression> _2922_dims = _2919___mcc_h7;
        {
          BigInteger _2923_i;
          _2923_i = (new BigInteger((_2922_dims).Count)) - (BigInteger.One);
          RAST._IType _2924_genTyp;
          RAST._IType _out1281;
          _out1281 = (this).GenType(_2921_typ, false, false);
          _2924_genTyp = _out1281;
          Dafny.ISequence<Dafny.Rune> _2925_s;
          _2925_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_2924_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_2923_i).Sign != -1) {
            RAST._IExpr _2926_recursiveGen;
            DCOMP._IOwnership _2927___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2928_recIdents;
            RAST._IExpr _out1282;
            DCOMP._IOwnership _out1283;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1284;
            (this).GenExpr((_2922_dims).Select(_2923_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1282, out _out1283, out _out1284);
            _2926_recursiveGen = _out1282;
            _2927___v86 = _out1283;
            _2928_recIdents = _out1284;
            _2925_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _2925_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_2926_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2928_recIdents);
            _2923_i = (_2923_i) - (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(_2925_s);
          RAST._IExpr _out1285;
          DCOMP._IOwnership _out1286;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1285, out _out1286);
          r = _out1285;
          resultingOwnership = _out1286;
          return ;
        }
      } else if (_source145.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2929___mcc_h9 = _source145.dtor_path;
        Dafny.ISequence<DAST._IType> _2930___mcc_h10 = _source145.dtor_typeArgs;
        Dafny.ISequence<Dafny.Rune> _2931___mcc_h11 = _source145.dtor_variant;
        bool _2932___mcc_h12 = _source145.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2933___mcc_h13 = _source145.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2934_values = _2933___mcc_h13;
        bool _2935_isCo = _2932___mcc_h12;
        Dafny.ISequence<Dafny.Rune> _2936_variant = _2931___mcc_h11;
        Dafny.ISequence<DAST._IType> _2937_typeArgs = _2930___mcc_h10;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2938_path = _2929___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _2939_path;
          Dafny.ISequence<Dafny.Rune> _out1287;
          _out1287 = DCOMP.COMP.GenPath(_2938_path);
          _2939_path = _out1287;
          Dafny.ISequence<Dafny.Rune> _2940_s;
          _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2939_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          if ((new BigInteger((_2937_typeArgs).Count)).Sign == 1) {
            _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
            BigInteger _2941_i;
            _2941_i = BigInteger.Zero;
            while ((_2941_i) < (new BigInteger((_2937_typeArgs).Count))) {
              if ((_2941_i).Sign == 1) {
                _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              RAST._IType _2942_typeExpr;
              RAST._IType _out1288;
              _out1288 = (this).GenType((_2937_typeArgs).Select(_2941_i), false, false);
              _2942_typeExpr = _out1288;
              _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, (_2942_typeExpr)._ToString(DCOMP.__default.IND));
              _2941_i = (_2941_i) + (BigInteger.One);
            }
            _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::"));
          }
          _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, DCOMP.__default.escapeIdent(_2936_variant));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2943_i;
          _2943_i = BigInteger.Zero;
          _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_2943_i) < (new BigInteger((_2934_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs60 = (_2934_values).Select(_2943_i);
            Dafny.ISequence<Dafny.Rune> _2944_name = _let_tmp_rhs60.dtor__0;
            DAST._IExpression _2945_value = _let_tmp_rhs60.dtor__1;
            if ((_2943_i).Sign == 1) {
              _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_2935_isCo) {
              RAST._IExpr _2946_recursiveGen;
              DCOMP._IOwnership _2947___v87;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2948_recIdents;
              RAST._IExpr _out1289;
              DCOMP._IOwnership _out1290;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1291;
              (this).GenExpr(_2945_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out1289, out _out1290, out _out1291);
              _2946_recursiveGen = _out1289;
              _2947___v87 = _out1290;
              _2948_recIdents = _out1291;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2948_recIdents);
              Dafny.ISequence<Dafny.Rune> _2949_allReadCloned;
              _2949_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_2948_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _2950_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_2948_recIdents).Elements) {
                  _2950_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                  if ((_2948_recIdents).Contains(_2950_next)) {
                    goto after__ASSIGN_SUCH_THAT_2;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 2852)");
              after__ASSIGN_SUCH_THAT_2: ;
                _2949_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2949_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent(_2950_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), DCOMP.__default.escapeIdent(_2950_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _2948_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2948_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2950_next));
              }
              _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, DCOMP.__default.escapeIdent(_2944_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _2949_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_2946_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              RAST._IExpr _2951_recursiveGen;
              DCOMP._IOwnership _2952___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2953_recIdents;
              RAST._IExpr _out1292;
              DCOMP._IOwnership _out1293;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1294;
              (this).GenExpr(_2945_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1292, out _out1293, out _out1294);
              _2951_recursiveGen = _out1292;
              _2952___v88 = _out1293;
              _2953_recIdents = _out1294;
              _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, DCOMP.__default.escapeIdent(_2944_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_2951_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2953_recIdents);
            }
            _2943_i = (_2943_i) + (BigInteger.One);
          }
          _2940_s = Dafny.Sequence<Dafny.Rune>.Concat(_2940_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          r = RAST.Expr.create_RawExpr(_2940_s);
          RAST._IExpr _out1295;
          DCOMP._IOwnership _out1296;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1295, out _out1296);
          r = _out1295;
          resultingOwnership = _out1296;
          return ;
        }
      } else if (_source145.is_Convert) {
        DAST._IExpression _2954___mcc_h14 = _source145.dtor_value;
        DAST._IType _2955___mcc_h15 = _source145.dtor_from;
        DAST._IType _2956___mcc_h16 = _source145.dtor_typ;
        {
          RAST._IExpr _out1297;
          DCOMP._IOwnership _out1298;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1299;
          (this).GenExprConvert(e, selfIdent, @params, expectedOwnership, out _out1297, out _out1298, out _out1299);
          r = _out1297;
          resultingOwnership = _out1298;
          readIdents = _out1299;
        }
      } else if (_source145.is_SeqConstruct) {
        DAST._IExpression _2957___mcc_h17 = _source145.dtor_length;
        DAST._IExpression _2958___mcc_h18 = _source145.dtor_elem;
        DAST._IExpression _2959_expr = _2958___mcc_h18;
        DAST._IExpression _2960_length = _2957___mcc_h17;
        {
          RAST._IExpr _2961_recursiveGen;
          DCOMP._IOwnership _2962___v92;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2963_recIdents;
          RAST._IExpr _out1300;
          DCOMP._IOwnership _out1301;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1302;
          (this).GenExpr(_2959_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1300, out _out1301, out _out1302);
          _2961_recursiveGen = _out1300;
          _2962___v92 = _out1301;
          _2963_recIdents = _out1302;
          RAST._IExpr _2964_lengthGen;
          DCOMP._IOwnership _2965___v93;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2966_lengthIdents;
          RAST._IExpr _out1303;
          DCOMP._IOwnership _out1304;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
          (this).GenExpr(_2960_length, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1303, out _out1304, out _out1305);
          _2964_lengthGen = _out1303;
          _2965___v93 = _out1304;
          _2966_lengthIdents = _out1305;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_2961_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_2964_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer.0(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2963_recIdents, _2966_lengthIdents);
          RAST._IExpr _out1306;
          DCOMP._IOwnership _out1307;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1306, out _out1307);
          r = _out1306;
          resultingOwnership = _out1307;
          return ;
        }
      } else if (_source145.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _2967___mcc_h19 = _source145.dtor_elements;
        DAST._IType _2968___mcc_h20 = _source145.dtor_typ;
        DAST._IType _2969_typ = _2968___mcc_h20;
        Dafny.ISequence<DAST._IExpression> _2970_exprs = _2967___mcc_h19;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IType _2971_genTpe;
          RAST._IType _out1308;
          _out1308 = (this).GenType(_2969_typ, false, false);
          _2971_genTpe = _out1308;
          BigInteger _2972_i;
          _2972_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _2973_args;
          _2973_args = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_2972_i) < (new BigInteger((_2970_exprs).Count))) {
            RAST._IExpr _2974_recursiveGen;
            DCOMP._IOwnership _2975___v94;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2976_recIdents;
            RAST._IExpr _out1309;
            DCOMP._IOwnership _out1310;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1311;
            (this).GenExpr((_2970_exprs).Select(_2972_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1309, out _out1310, out _out1311);
            _2974_recursiveGen = _out1309;
            _2975___v94 = _out1310;
            _2976_recIdents = _out1311;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2976_recIdents);
            _2973_args = Dafny.Sequence<RAST._IExpr>.Concat(_2973_args, Dafny.Sequence<RAST._IExpr>.FromElements(_2974_recursiveGen));
            _2972_i = (_2972_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _2973_args);
          if ((new BigInteger((_2973_args).Count)).Sign == 0) {
            r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_2971_genTpe));
          }
          RAST._IExpr _out1312;
          DCOMP._IOwnership _out1313;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1312, out _out1313);
          r = _out1312;
          resultingOwnership = _out1313;
          return ;
        }
      } else if (_source145.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _2977___mcc_h21 = _source145.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2978_exprs = _2977___mcc_h21;
        {
          Dafny.ISequence<RAST._IExpr> _2979_generatedValues;
          _2979_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2980_i;
          _2980_i = BigInteger.Zero;
          while ((_2980_i) < (new BigInteger((_2978_exprs).Count))) {
            RAST._IExpr _2981_recursiveGen;
            DCOMP._IOwnership _2982___v95;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2983_recIdents;
            RAST._IExpr _out1314;
            DCOMP._IOwnership _out1315;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1316;
            (this).GenExpr((_2978_exprs).Select(_2980_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1314, out _out1315, out _out1316);
            _2981_recursiveGen = _out1314;
            _2982___v95 = _out1315;
            _2983_recIdents = _out1316;
            _2979_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2979_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2981_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2983_recIdents);
            _2980_i = (_2980_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _2979_generatedValues);
          RAST._IExpr _out1317;
          DCOMP._IOwnership _out1318;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1317, out _out1318);
          r = _out1317;
          resultingOwnership = _out1318;
          return ;
        }
      } else if (_source145.is_MultisetValue) {
        Dafny.ISequence<DAST._IExpression> _2984___mcc_h22 = _source145.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2985_exprs = _2984___mcc_h22;
        {
          Dafny.ISequence<RAST._IExpr> _2986_generatedValues;
          _2986_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2987_i;
          _2987_i = BigInteger.Zero;
          while ((_2987_i) < (new BigInteger((_2985_exprs).Count))) {
            RAST._IExpr _2988_recursiveGen;
            DCOMP._IOwnership _2989___v96;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2990_recIdents;
            RAST._IExpr _out1319;
            DCOMP._IOwnership _out1320;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1321;
            (this).GenExpr((_2985_exprs).Select(_2987_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1319, out _out1320, out _out1321);
            _2988_recursiveGen = _out1319;
            _2989___v96 = _out1320;
            _2990_recIdents = _out1321;
            _2986_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2986_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2988_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2990_recIdents);
            _2987_i = (_2987_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _2986_generatedValues);
          RAST._IExpr _out1322;
          DCOMP._IOwnership _out1323;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1322, out _out1323);
          r = _out1322;
          resultingOwnership = _out1323;
          return ;
        }
      } else if (_source145.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2991___mcc_h23 = _source145.dtor_mapElems;
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2992_mapElems = _2991___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _2993_generatedValues;
          _2993_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2994_i;
          _2994_i = BigInteger.Zero;
          while ((_2994_i) < (new BigInteger((_2992_mapElems).Count))) {
            RAST._IExpr _2995_recursiveGenKey;
            DCOMP._IOwnership _2996___v98;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2997_recIdentsKey;
            RAST._IExpr _out1324;
            DCOMP._IOwnership _out1325;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1326;
            (this).GenExpr(((_2992_mapElems).Select(_2994_i)).dtor__0, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1324, out _out1325, out _out1326);
            _2995_recursiveGenKey = _out1324;
            _2996___v98 = _out1325;
            _2997_recIdentsKey = _out1326;
            RAST._IExpr _2998_recursiveGenValue;
            DCOMP._IOwnership _2999___v99;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3000_recIdentsValue;
            RAST._IExpr _out1327;
            DCOMP._IOwnership _out1328;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1329;
            (this).GenExpr(((_2992_mapElems).Select(_2994_i)).dtor__1, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1327, out _out1328, out _out1329);
            _2998_recursiveGenValue = _out1327;
            _2999___v99 = _out1328;
            _3000_recIdentsValue = _out1329;
            _2993_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_2993_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_2995_recursiveGenKey, _2998_recursiveGenValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2997_recIdentsKey), _3000_recIdentsValue);
            _2994_i = (_2994_i) + (BigInteger.One);
          }
          _2994_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _3001_arguments;
          _3001_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_2994_i) < (new BigInteger((_2993_generatedValues).Count))) {
            RAST._IExpr _3002_genKey;
            _3002_genKey = ((_2993_generatedValues).Select(_2994_i)).dtor__0;
            RAST._IExpr _3003_genValue;
            _3003_genValue = ((_2993_generatedValues).Select(_2994_i)).dtor__1;
            _3001_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3001_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _3002_genKey, _3003_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
            _2994_i = (_2994_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3001_arguments);
          RAST._IExpr _out1330;
          DCOMP._IOwnership _out1331;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1330, out _out1331);
          r = _out1330;
          resultingOwnership = _out1331;
          return ;
        }
      } else if (_source145.is_MapBuilder) {
        DAST._IType _3004___mcc_h24 = _source145.dtor_keyType;
        DAST._IType _3005___mcc_h25 = _source145.dtor_valueType;
        DAST._IType _3006_valueType = _3005___mcc_h25;
        DAST._IType _3007_keyType = _3004___mcc_h24;
        {
          RAST._IType _3008_kType;
          RAST._IType _out1332;
          _out1332 = (this).GenType(_3007_keyType, false, false);
          _3008_kType = _out1332;
          RAST._IType _3009_vType;
          RAST._IType _out1333;
          _out1333 = (this).GenType(_3006_valueType, false, false);
          _3009_vType = _out1333;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::MapBuilder::<"), (_3008_kType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), (_3009_vType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::new()")));
          RAST._IExpr _out1334;
          DCOMP._IOwnership _out1335;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1334, out _out1335);
          r = _out1334;
          resultingOwnership = _out1335;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source145.is_SeqUpdate) {
        DAST._IExpression _3010___mcc_h26 = _source145.dtor_expr;
        DAST._IExpression _3011___mcc_h27 = _source145.dtor_indexExpr;
        DAST._IExpression _3012___mcc_h28 = _source145.dtor_value;
        DAST._IExpression _3013_value = _3012___mcc_h28;
        DAST._IExpression _3014_index = _3011___mcc_h27;
        DAST._IExpression _3015_expr = _3010___mcc_h26;
        {
          RAST._IExpr _3016_exprR;
          DCOMP._IOwnership _3017___v100;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3018_exprIdents;
          RAST._IExpr _out1336;
          DCOMP._IOwnership _out1337;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1338;
          (this).GenExpr(_3015_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1336, out _out1337, out _out1338);
          _3016_exprR = _out1336;
          _3017___v100 = _out1337;
          _3018_exprIdents = _out1338;
          RAST._IExpr _3019_indexR;
          DCOMP._IOwnership _3020_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3021_indexIdents;
          RAST._IExpr _out1339;
          DCOMP._IOwnership _out1340;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1341;
          (this).GenExpr(_3014_index, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1339, out _out1340, out _out1341);
          _3019_indexR = _out1339;
          _3020_indexOwnership = _out1340;
          _3021_indexIdents = _out1341;
          RAST._IExpr _3022_valueR;
          DCOMP._IOwnership _3023_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3024_valueIdents;
          RAST._IExpr _out1342;
          DCOMP._IOwnership _out1343;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1344;
          (this).GenExpr(_3013_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1342, out _out1343, out _out1344);
          _3022_valueR = _out1342;
          _3023_valueOwnership = _out1343;
          _3024_valueIdents = _out1344;
          r = ((_3016_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_3019_indexR, _3022_valueR));
          RAST._IExpr _out1345;
          DCOMP._IOwnership _out1346;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1345, out _out1346);
          r = _out1345;
          resultingOwnership = _out1346;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3018_exprIdents, _3021_indexIdents), _3024_valueIdents);
          return ;
        }
      } else if (_source145.is_MapUpdate) {
        DAST._IExpression _3025___mcc_h29 = _source145.dtor_expr;
        DAST._IExpression _3026___mcc_h30 = _source145.dtor_indexExpr;
        DAST._IExpression _3027___mcc_h31 = _source145.dtor_value;
        DAST._IExpression _3028_value = _3027___mcc_h31;
        DAST._IExpression _3029_index = _3026___mcc_h30;
        DAST._IExpression _3030_expr = _3025___mcc_h29;
        {
          RAST._IExpr _3031_exprR;
          DCOMP._IOwnership _3032___v101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3033_exprIdents;
          RAST._IExpr _out1347;
          DCOMP._IOwnership _out1348;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1349;
          (this).GenExpr(_3030_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1347, out _out1348, out _out1349);
          _3031_exprR = _out1347;
          _3032___v101 = _out1348;
          _3033_exprIdents = _out1349;
          RAST._IExpr _3034_indexR;
          DCOMP._IOwnership _3035_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3036_indexIdents;
          RAST._IExpr _out1350;
          DCOMP._IOwnership _out1351;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1352;
          (this).GenExpr(_3029_index, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1350, out _out1351, out _out1352);
          _3034_indexR = _out1350;
          _3035_indexOwnership = _out1351;
          _3036_indexIdents = _out1352;
          RAST._IExpr _3037_valueR;
          DCOMP._IOwnership _3038_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3039_valueIdents;
          RAST._IExpr _out1353;
          DCOMP._IOwnership _out1354;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1355;
          (this).GenExpr(_3028_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1353, out _out1354, out _out1355);
          _3037_valueR = _out1353;
          _3038_valueOwnership = _out1354;
          _3039_valueIdents = _out1355;
          r = ((_3031_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_3034_indexR, _3037_valueR));
          RAST._IExpr _out1356;
          DCOMP._IOwnership _out1357;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1356, out _out1357);
          r = _out1356;
          resultingOwnership = _out1357;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3033_exprIdents, _3036_indexIdents), _3039_valueIdents);
          return ;
        }
      } else if (_source145.is_SetBuilder) {
        DAST._IType _3040___mcc_h32 = _source145.dtor_elemType;
        DAST._IType _3041_elemType = _3040___mcc_h32;
        {
          RAST._IType _3042_eType;
          RAST._IType _out1358;
          _out1358 = (this).GenType(_3041_elemType, false, false);
          _3042_eType = _out1358;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::SetBuilder::<"), (_3042_eType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::new()")));
          RAST._IExpr _out1359;
          DCOMP._IOwnership _out1360;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1359, out _out1360);
          r = _out1359;
          resultingOwnership = _out1360;
          return ;
        }
      } else if (_source145.is_ToMultiset) {
        DAST._IExpression _3043___mcc_h33 = _source145.dtor_ToMultiset_a0;
        DAST._IExpression _3044_expr = _3043___mcc_h33;
        {
          RAST._IExpr _3045_recursiveGen;
          DCOMP._IOwnership _3046___v97;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3047_recIdents;
          RAST._IExpr _out1361;
          DCOMP._IOwnership _out1362;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1363;
          (this).GenExpr(_3044_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1361, out _out1362, out _out1363);
          _3045_recursiveGen = _out1361;
          _3046___v97 = _out1362;
          _3047_recIdents = _out1363;
          r = ((_3045_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          readIdents = _3047_recIdents;
          RAST._IExpr _out1364;
          DCOMP._IOwnership _out1365;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1364, out _out1365);
          r = _out1364;
          resultingOwnership = _out1365;
          return ;
        }
      } else if (_source145.is_This) {
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source146 = selfIdent;
          if (_source146.is_None) {
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
            Dafny.ISequence<Dafny.Rune> _3048___mcc_h273 = _source146.dtor_value;
            Dafny.ISequence<Dafny.Rune> _3049_id = _3048___mcc_h273;
            {
              r = RAST.Expr.create_RawExpr(_3049_id);
              if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                r = RAST.__default.Clone(r);
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                if (!(_3049_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.Borrow(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              } else {
                if (!(_3049_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.BorrowMut(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3049_id);
            }
          }
          return ;
        }
      } else if (_source145.is_Ite) {
        DAST._IExpression _3050___mcc_h34 = _source145.dtor_cond;
        DAST._IExpression _3051___mcc_h35 = _source145.dtor_thn;
        DAST._IExpression _3052___mcc_h36 = _source145.dtor_els;
        DAST._IExpression _3053_f = _3052___mcc_h36;
        DAST._IExpression _3054_t = _3051___mcc_h35;
        DAST._IExpression _3055_cond = _3050___mcc_h34;
        {
          RAST._IExpr _3056_cond;
          DCOMP._IOwnership _3057___v102;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3058_recIdentsCond;
          RAST._IExpr _out1368;
          DCOMP._IOwnership _out1369;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1370;
          (this).GenExpr(_3055_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1368, out _out1369, out _out1370);
          _3056_cond = _out1368;
          _3057___v102 = _out1369;
          _3058_recIdentsCond = _out1370;
          Dafny.ISequence<Dafny.Rune> _3059_condString;
          _3059_condString = (_3056_cond)._ToString(DCOMP.__default.IND);
          RAST._IExpr _3060___v103;
          DCOMP._IOwnership _3061_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3062___v104;
          RAST._IExpr _out1371;
          DCOMP._IOwnership _out1372;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1373;
          (this).GenExpr(_3054_t, selfIdent, @params, expectedOwnership, out _out1371, out _out1372, out _out1373);
          _3060___v103 = _out1371;
          _3061_tHasToBeOwned = _out1372;
          _3062___v104 = _out1373;
          RAST._IExpr _3063_fExpr;
          DCOMP._IOwnership _3064_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3065_recIdentsF;
          RAST._IExpr _out1374;
          DCOMP._IOwnership _out1375;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1376;
          (this).GenExpr(_3053_f, selfIdent, @params, _3061_tHasToBeOwned, out _out1374, out _out1375, out _out1376);
          _3063_fExpr = _out1374;
          _3064_fOwned = _out1375;
          _3065_recIdentsF = _out1376;
          Dafny.ISequence<Dafny.Rune> _3066_fString;
          _3066_fString = (_3063_fExpr)._ToString(DCOMP.__default.IND);
          RAST._IExpr _3067_tExpr;
          DCOMP._IOwnership _3068___v105;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3069_recIdentsT;
          RAST._IExpr _out1377;
          DCOMP._IOwnership _out1378;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1379;
          (this).GenExpr(_3054_t, selfIdent, @params, _3064_fOwned, out _out1377, out _out1378, out _out1379);
          _3067_tExpr = _out1377;
          _3068___v105 = _out1378;
          _3069_recIdentsT = _out1379;
          Dafny.ISequence<Dafny.Rune> _3070_tString;
          _3070_tString = (_3067_tExpr)._ToString(DCOMP.__default.IND);
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _3059_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _3070_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _3066_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
          RAST._IExpr _out1380;
          DCOMP._IOwnership _out1381;
          DCOMP.COMP.FromOwnership(r, _3064_fOwned, expectedOwnership, out _out1380, out _out1381);
          r = _out1380;
          resultingOwnership = _out1381;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3058_recIdentsCond, _3069_recIdentsT), _3065_recIdentsF);
          return ;
        }
      } else if (_source145.is_UnOp) {
        DAST._IUnaryOp _3071___mcc_h37 = _source145.dtor_unOp;
        DAST._IExpression _3072___mcc_h38 = _source145.dtor_expr;
        DAST.Format._IUnaryOpFormat _3073___mcc_h39 = _source145.dtor_format1;
        DAST._IUnaryOp _source147 = _3071___mcc_h37;
        if (_source147.is_Not) {
          DAST.Format._IUnaryOpFormat _3074_format = _3073___mcc_h39;
          DAST._IExpression _3075_e = _3072___mcc_h38;
          {
            RAST._IExpr _3076_recursiveGen;
            DCOMP._IOwnership _3077___v106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3078_recIdents;
            RAST._IExpr _out1382;
            DCOMP._IOwnership _out1383;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1384;
            (this).GenExpr(_3075_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1382, out _out1383, out _out1384);
            _3076_recursiveGen = _out1382;
            _3077___v106 = _out1383;
            _3078_recIdents = _out1384;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _3076_recursiveGen, _3074_format);
            RAST._IExpr _out1385;
            DCOMP._IOwnership _out1386;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1385, out _out1386);
            r = _out1385;
            resultingOwnership = _out1386;
            readIdents = _3078_recIdents;
            return ;
          }
        } else if (_source147.is_BitwiseNot) {
          DAST.Format._IUnaryOpFormat _3079_format = _3073___mcc_h39;
          DAST._IExpression _3080_e = _3072___mcc_h38;
          {
            RAST._IExpr _3081_recursiveGen;
            DCOMP._IOwnership _3082___v107;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3083_recIdents;
            RAST._IExpr _out1387;
            DCOMP._IOwnership _out1388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1389;
            (this).GenExpr(_3080_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1387, out _out1388, out _out1389);
            _3081_recursiveGen = _out1387;
            _3082___v107 = _out1388;
            _3083_recIdents = _out1389;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _3081_recursiveGen, _3079_format);
            RAST._IExpr _out1390;
            DCOMP._IOwnership _out1391;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1390, out _out1391);
            r = _out1390;
            resultingOwnership = _out1391;
            readIdents = _3083_recIdents;
            return ;
          }
        } else {
          DAST.Format._IUnaryOpFormat _3084_format = _3073___mcc_h39;
          DAST._IExpression _3085_e = _3072___mcc_h38;
          {
            RAST._IExpr _3086_recursiveGen;
            DCOMP._IOwnership _3087_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3088_recIdents;
            RAST._IExpr _out1392;
            DCOMP._IOwnership _out1393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1394;
            (this).GenExpr(_3085_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1392, out _out1393, out _out1394);
            _3086_recursiveGen = _out1392;
            _3087_recOwned = _out1393;
            _3088_recIdents = _out1394;
            r = ((_3086_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1395;
            DCOMP._IOwnership _out1396;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1395, out _out1396);
            r = _out1395;
            resultingOwnership = _out1396;
            readIdents = _3088_recIdents;
            return ;
          }
        }
      } else if (_source145.is_BinOp) {
        DAST._IBinOp _3089___mcc_h40 = _source145.dtor_op;
        DAST._IExpression _3090___mcc_h41 = _source145.dtor_left;
        DAST._IExpression _3091___mcc_h42 = _source145.dtor_right;
        DAST.Format._IBinaryOpFormat _3092___mcc_h43 = _source145.dtor_format2;
        RAST._IExpr _out1397;
        DCOMP._IOwnership _out1398;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1399;
        (this).GenExprBinary(e, selfIdent, @params, expectedOwnership, out _out1397, out _out1398, out _out1399);
        r = _out1397;
        resultingOwnership = _out1398;
        readIdents = _out1399;
      } else if (_source145.is_ArrayLen) {
        DAST._IExpression _3093___mcc_h44 = _source145.dtor_expr;
        BigInteger _3094___mcc_h45 = _source145.dtor_dim;
        BigInteger _3095_dim = _3094___mcc_h45;
        DAST._IExpression _3096_expr = _3093___mcc_h44;
        {
          RAST._IExpr _3097_recursiveGen;
          DCOMP._IOwnership _3098___v112;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3099_recIdents;
          RAST._IExpr _out1400;
          DCOMP._IOwnership _out1401;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1402;
          (this).GenExpr(_3096_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1400, out _out1401, out _out1402);
          _3097_recursiveGen = _out1400;
          _3098___v112 = _out1401;
          _3099_recIdents = _out1402;
          if ((_3095_dim).Sign == 0) {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_3097_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
          } else {
            Dafny.ISequence<Dafny.Rune> _3100_s;
            _3100_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
            BigInteger _3101_i;
            _3101_i = BigInteger.One;
            while ((_3101_i) < (_3095_dim)) {
              _3100_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _3100_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
              _3101_i = (_3101_i) + (BigInteger.One);
            }
            r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_3097_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _3100_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
          }
          RAST._IExpr _out1403;
          DCOMP._IOwnership _out1404;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1403, out _out1404);
          r = _out1403;
          resultingOwnership = _out1404;
          readIdents = _3099_recIdents;
          return ;
        }
      } else if (_source145.is_MapKeys) {
        DAST._IExpression _3102___mcc_h46 = _source145.dtor_expr;
        DAST._IExpression _3103_expr = _3102___mcc_h46;
        {
          RAST._IExpr _3104_recursiveGen;
          DCOMP._IOwnership _3105___v113;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3106_recIdents;
          RAST._IExpr _out1405;
          DCOMP._IOwnership _out1406;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1407;
          (this).GenExpr(_3103_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1405, out _out1406, out _out1407);
          _3104_recursiveGen = _out1405;
          _3105___v113 = _out1406;
          _3106_recIdents = _out1407;
          readIdents = _3106_recIdents;
          r = RAST.Expr.create_Call((_3104_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1408;
          DCOMP._IOwnership _out1409;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1408, out _out1409);
          r = _out1408;
          resultingOwnership = _out1409;
          return ;
        }
      } else if (_source145.is_MapValues) {
        DAST._IExpression _3107___mcc_h47 = _source145.dtor_expr;
        DAST._IExpression _3108_expr = _3107___mcc_h47;
        {
          RAST._IExpr _3109_recursiveGen;
          DCOMP._IOwnership _3110___v114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3111_recIdents;
          RAST._IExpr _out1410;
          DCOMP._IOwnership _out1411;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1412;
          (this).GenExpr(_3108_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1410, out _out1411, out _out1412);
          _3109_recursiveGen = _out1410;
          _3110___v114 = _out1411;
          _3111_recIdents = _out1412;
          readIdents = _3111_recIdents;
          r = RAST.Expr.create_Call((_3109_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1413;
          DCOMP._IOwnership _out1414;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1413, out _out1414);
          r = _out1413;
          resultingOwnership = _out1414;
          return ;
        }
      } else if (_source145.is_Select) {
        DAST._IExpression _3112___mcc_h48 = _source145.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _3113___mcc_h49 = _source145.dtor_field;
        bool _3114___mcc_h50 = _source145.dtor_isConstant;
        bool _3115___mcc_h51 = _source145.dtor_onDatatype;
        DAST._IExpression _source148 = _3112___mcc_h48;
        if (_source148.is_Literal) {
          DAST._ILiteral _3116___mcc_h52 = _source148.dtor_Literal_a0;
          bool _3117_isDatatype = _3115___mcc_h51;
          bool _3118_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3119_field = _3113___mcc_h49;
          DAST._IExpression _3120_on = _3112___mcc_h48;
          {
            RAST._IExpr _3121_onExpr;
            DCOMP._IOwnership _3122_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3123_recIdents;
            RAST._IExpr _out1415;
            DCOMP._IOwnership _out1416;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1417;
            (this).GenExpr(_3120_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1415, out _out1416, out _out1417);
            _3121_onExpr = _out1415;
            _3122_onOwned = _out1416;
            _3123_recIdents = _out1417;
            if ((_3117_isDatatype) || (_3118_isConstant)) {
              r = RAST.Expr.create_Call((_3121_onExpr).Sel(DCOMP.__default.escapeIdent(_3119_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1418;
              DCOMP._IOwnership _out1419;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1418, out _out1419);
              r = _out1418;
              resultingOwnership = _out1419;
            } else {
              Dafny.ISequence<Dafny.Rune> _3124_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3124_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3121_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3119_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1420;
              DCOMP._IOwnership _out1421;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3124_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1420, out _out1421);
              r = _out1420;
              resultingOwnership = _out1421;
            }
            readIdents = _3123_recIdents;
            return ;
          }
        } else if (_source148.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _3125___mcc_h54 = _source148.dtor_Ident_a0;
          bool _3126_isDatatype = _3115___mcc_h51;
          bool _3127_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3128_field = _3113___mcc_h49;
          DAST._IExpression _3129_on = _3112___mcc_h48;
          {
            RAST._IExpr _3130_onExpr;
            DCOMP._IOwnership _3131_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3132_recIdents;
            RAST._IExpr _out1422;
            DCOMP._IOwnership _out1423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1424;
            (this).GenExpr(_3129_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1422, out _out1423, out _out1424);
            _3130_onExpr = _out1422;
            _3131_onOwned = _out1423;
            _3132_recIdents = _out1424;
            if ((_3126_isDatatype) || (_3127_isConstant)) {
              r = RAST.Expr.create_Call((_3130_onExpr).Sel(DCOMP.__default.escapeIdent(_3128_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1425;
              DCOMP._IOwnership _out1426;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1425, out _out1426);
              r = _out1425;
              resultingOwnership = _out1426;
            } else {
              Dafny.ISequence<Dafny.Rune> _3133_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3133_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3130_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3128_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1427;
              DCOMP._IOwnership _out1428;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3133_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1427, out _out1428);
              r = _out1427;
              resultingOwnership = _out1428;
            }
            readIdents = _3132_recIdents;
            return ;
          }
        } else if (_source148.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3134___mcc_h56 = _source148.dtor_Companion_a0;
          bool _3135_isDatatype = _3115___mcc_h51;
          bool _3136_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3137_field = _3113___mcc_h49;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3138_c = _3134___mcc_h56;
          {
            RAST._IExpr _3139_onExpr;
            DCOMP._IOwnership _3140_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3141_recIdents;
            RAST._IExpr _out1429;
            DCOMP._IOwnership _out1430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1431;
            (this).GenExpr(DAST.Expression.create_Companion(_3138_c), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1429, out _out1430, out _out1431);
            _3139_onExpr = _out1429;
            _3140_onOwned = _out1430;
            _3141_recIdents = _out1431;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_3139_onExpr)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_3137_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")));
            RAST._IExpr _out1432;
            DCOMP._IOwnership _out1433;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1432, out _out1433);
            r = _out1432;
            resultingOwnership = _out1433;
            readIdents = _3141_recIdents;
            return ;
          }
        } else if (_source148.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _3142___mcc_h58 = _source148.dtor_Tuple_a0;
          bool _3143_isDatatype = _3115___mcc_h51;
          bool _3144_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3145_field = _3113___mcc_h49;
          DAST._IExpression _3146_on = _3112___mcc_h48;
          {
            RAST._IExpr _3147_onExpr;
            DCOMP._IOwnership _3148_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3149_recIdents;
            RAST._IExpr _out1434;
            DCOMP._IOwnership _out1435;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1436;
            (this).GenExpr(_3146_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1434, out _out1435, out _out1436);
            _3147_onExpr = _out1434;
            _3148_onOwned = _out1435;
            _3149_recIdents = _out1436;
            if ((_3143_isDatatype) || (_3144_isConstant)) {
              r = RAST.Expr.create_Call((_3147_onExpr).Sel(DCOMP.__default.escapeIdent(_3145_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1437;
              DCOMP._IOwnership _out1438;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1437, out _out1438);
              r = _out1437;
              resultingOwnership = _out1438;
            } else {
              Dafny.ISequence<Dafny.Rune> _3150_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3150_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3147_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3145_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1439;
              DCOMP._IOwnership _out1440;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3150_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1439, out _out1440);
              r = _out1439;
              resultingOwnership = _out1440;
            }
            readIdents = _3149_recIdents;
            return ;
          }
        } else if (_source148.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3151___mcc_h60 = _source148.dtor_path;
          Dafny.ISequence<DAST._IType> _3152___mcc_h61 = _source148.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _3153___mcc_h62 = _source148.dtor_args;
          bool _3154_isDatatype = _3115___mcc_h51;
          bool _3155_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3156_field = _3113___mcc_h49;
          DAST._IExpression _3157_on = _3112___mcc_h48;
          {
            RAST._IExpr _3158_onExpr;
            DCOMP._IOwnership _3159_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3160_recIdents;
            RAST._IExpr _out1441;
            DCOMP._IOwnership _out1442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1443;
            (this).GenExpr(_3157_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1441, out _out1442, out _out1443);
            _3158_onExpr = _out1441;
            _3159_onOwned = _out1442;
            _3160_recIdents = _out1443;
            if ((_3154_isDatatype) || (_3155_isConstant)) {
              r = RAST.Expr.create_Call((_3158_onExpr).Sel(DCOMP.__default.escapeIdent(_3156_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1444;
              DCOMP._IOwnership _out1445;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1444, out _out1445);
              r = _out1444;
              resultingOwnership = _out1445;
            } else {
              Dafny.ISequence<Dafny.Rune> _3161_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3161_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3158_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3156_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1446;
              DCOMP._IOwnership _out1447;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3161_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1446, out _out1447);
              r = _out1446;
              resultingOwnership = _out1447;
            }
            readIdents = _3160_recIdents;
            return ;
          }
        } else if (_source148.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _3162___mcc_h66 = _source148.dtor_dims;
          DAST._IType _3163___mcc_h67 = _source148.dtor_typ;
          bool _3164_isDatatype = _3115___mcc_h51;
          bool _3165_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3166_field = _3113___mcc_h49;
          DAST._IExpression _3167_on = _3112___mcc_h48;
          {
            RAST._IExpr _3168_onExpr;
            DCOMP._IOwnership _3169_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3170_recIdents;
            RAST._IExpr _out1448;
            DCOMP._IOwnership _out1449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1450;
            (this).GenExpr(_3167_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1448, out _out1449, out _out1450);
            _3168_onExpr = _out1448;
            _3169_onOwned = _out1449;
            _3170_recIdents = _out1450;
            if ((_3164_isDatatype) || (_3165_isConstant)) {
              r = RAST.Expr.create_Call((_3168_onExpr).Sel(DCOMP.__default.escapeIdent(_3166_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1451;
              DCOMP._IOwnership _out1452;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1451, out _out1452);
              r = _out1451;
              resultingOwnership = _out1452;
            } else {
              Dafny.ISequence<Dafny.Rune> _3171_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3171_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3168_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3166_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1453;
              DCOMP._IOwnership _out1454;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3171_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1453, out _out1454);
              r = _out1453;
              resultingOwnership = _out1454;
            }
            readIdents = _3170_recIdents;
            return ;
          }
        } else if (_source148.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3172___mcc_h70 = _source148.dtor_path;
          Dafny.ISequence<DAST._IType> _3173___mcc_h71 = _source148.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _3174___mcc_h72 = _source148.dtor_variant;
          bool _3175___mcc_h73 = _source148.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3176___mcc_h74 = _source148.dtor_contents;
          bool _3177_isDatatype = _3115___mcc_h51;
          bool _3178_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3179_field = _3113___mcc_h49;
          DAST._IExpression _3180_on = _3112___mcc_h48;
          {
            RAST._IExpr _3181_onExpr;
            DCOMP._IOwnership _3182_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3183_recIdents;
            RAST._IExpr _out1455;
            DCOMP._IOwnership _out1456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1457;
            (this).GenExpr(_3180_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1455, out _out1456, out _out1457);
            _3181_onExpr = _out1455;
            _3182_onOwned = _out1456;
            _3183_recIdents = _out1457;
            if ((_3177_isDatatype) || (_3178_isConstant)) {
              r = RAST.Expr.create_Call((_3181_onExpr).Sel(DCOMP.__default.escapeIdent(_3179_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1458;
              DCOMP._IOwnership _out1459;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1458, out _out1459);
              r = _out1458;
              resultingOwnership = _out1459;
            } else {
              Dafny.ISequence<Dafny.Rune> _3184_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3184_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3181_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3179_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1460;
              DCOMP._IOwnership _out1461;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3184_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1460, out _out1461);
              r = _out1460;
              resultingOwnership = _out1461;
            }
            readIdents = _3183_recIdents;
            return ;
          }
        } else if (_source148.is_Convert) {
          DAST._IExpression _3185___mcc_h80 = _source148.dtor_value;
          DAST._IType _3186___mcc_h81 = _source148.dtor_from;
          DAST._IType _3187___mcc_h82 = _source148.dtor_typ;
          bool _3188_isDatatype = _3115___mcc_h51;
          bool _3189_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3190_field = _3113___mcc_h49;
          DAST._IExpression _3191_on = _3112___mcc_h48;
          {
            RAST._IExpr _3192_onExpr;
            DCOMP._IOwnership _3193_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3194_recIdents;
            RAST._IExpr _out1462;
            DCOMP._IOwnership _out1463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1464;
            (this).GenExpr(_3191_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1462, out _out1463, out _out1464);
            _3192_onExpr = _out1462;
            _3193_onOwned = _out1463;
            _3194_recIdents = _out1464;
            if ((_3188_isDatatype) || (_3189_isConstant)) {
              r = RAST.Expr.create_Call((_3192_onExpr).Sel(DCOMP.__default.escapeIdent(_3190_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1465;
              DCOMP._IOwnership _out1466;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1465, out _out1466);
              r = _out1465;
              resultingOwnership = _out1466;
            } else {
              Dafny.ISequence<Dafny.Rune> _3195_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3195_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3192_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3190_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1467;
              DCOMP._IOwnership _out1468;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3195_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1467, out _out1468);
              r = _out1467;
              resultingOwnership = _out1468;
            }
            readIdents = _3194_recIdents;
            return ;
          }
        } else if (_source148.is_SeqConstruct) {
          DAST._IExpression _3196___mcc_h86 = _source148.dtor_length;
          DAST._IExpression _3197___mcc_h87 = _source148.dtor_elem;
          bool _3198_isDatatype = _3115___mcc_h51;
          bool _3199_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3200_field = _3113___mcc_h49;
          DAST._IExpression _3201_on = _3112___mcc_h48;
          {
            RAST._IExpr _3202_onExpr;
            DCOMP._IOwnership _3203_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3204_recIdents;
            RAST._IExpr _out1469;
            DCOMP._IOwnership _out1470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1471;
            (this).GenExpr(_3201_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1469, out _out1470, out _out1471);
            _3202_onExpr = _out1469;
            _3203_onOwned = _out1470;
            _3204_recIdents = _out1471;
            if ((_3198_isDatatype) || (_3199_isConstant)) {
              r = RAST.Expr.create_Call((_3202_onExpr).Sel(DCOMP.__default.escapeIdent(_3200_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1472;
              DCOMP._IOwnership _out1473;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1472, out _out1473);
              r = _out1472;
              resultingOwnership = _out1473;
            } else {
              Dafny.ISequence<Dafny.Rune> _3205_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3205_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3202_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3200_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1474;
              DCOMP._IOwnership _out1475;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3205_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1474, out _out1475);
              r = _out1474;
              resultingOwnership = _out1475;
            }
            readIdents = _3204_recIdents;
            return ;
          }
        } else if (_source148.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _3206___mcc_h90 = _source148.dtor_elements;
          DAST._IType _3207___mcc_h91 = _source148.dtor_typ;
          bool _3208_isDatatype = _3115___mcc_h51;
          bool _3209_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3210_field = _3113___mcc_h49;
          DAST._IExpression _3211_on = _3112___mcc_h48;
          {
            RAST._IExpr _3212_onExpr;
            DCOMP._IOwnership _3213_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3214_recIdents;
            RAST._IExpr _out1476;
            DCOMP._IOwnership _out1477;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1478;
            (this).GenExpr(_3211_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1476, out _out1477, out _out1478);
            _3212_onExpr = _out1476;
            _3213_onOwned = _out1477;
            _3214_recIdents = _out1478;
            if ((_3208_isDatatype) || (_3209_isConstant)) {
              r = RAST.Expr.create_Call((_3212_onExpr).Sel(DCOMP.__default.escapeIdent(_3210_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1479;
              DCOMP._IOwnership _out1480;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1479, out _out1480);
              r = _out1479;
              resultingOwnership = _out1480;
            } else {
              Dafny.ISequence<Dafny.Rune> _3215_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3215_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3212_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3210_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1481;
              DCOMP._IOwnership _out1482;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3215_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1481, out _out1482);
              r = _out1481;
              resultingOwnership = _out1482;
            }
            readIdents = _3214_recIdents;
            return ;
          }
        } else if (_source148.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _3216___mcc_h94 = _source148.dtor_elements;
          bool _3217_isDatatype = _3115___mcc_h51;
          bool _3218_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3219_field = _3113___mcc_h49;
          DAST._IExpression _3220_on = _3112___mcc_h48;
          {
            RAST._IExpr _3221_onExpr;
            DCOMP._IOwnership _3222_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3223_recIdents;
            RAST._IExpr _out1483;
            DCOMP._IOwnership _out1484;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1485;
            (this).GenExpr(_3220_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1483, out _out1484, out _out1485);
            _3221_onExpr = _out1483;
            _3222_onOwned = _out1484;
            _3223_recIdents = _out1485;
            if ((_3217_isDatatype) || (_3218_isConstant)) {
              r = RAST.Expr.create_Call((_3221_onExpr).Sel(DCOMP.__default.escapeIdent(_3219_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1486;
              DCOMP._IOwnership _out1487;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1486, out _out1487);
              r = _out1486;
              resultingOwnership = _out1487;
            } else {
              Dafny.ISequence<Dafny.Rune> _3224_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3224_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3221_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3219_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1488;
              DCOMP._IOwnership _out1489;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3224_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1488, out _out1489);
              r = _out1488;
              resultingOwnership = _out1489;
            }
            readIdents = _3223_recIdents;
            return ;
          }
        } else if (_source148.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _3225___mcc_h96 = _source148.dtor_elements;
          bool _3226_isDatatype = _3115___mcc_h51;
          bool _3227_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3228_field = _3113___mcc_h49;
          DAST._IExpression _3229_on = _3112___mcc_h48;
          {
            RAST._IExpr _3230_onExpr;
            DCOMP._IOwnership _3231_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3232_recIdents;
            RAST._IExpr _out1490;
            DCOMP._IOwnership _out1491;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1492;
            (this).GenExpr(_3229_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1490, out _out1491, out _out1492);
            _3230_onExpr = _out1490;
            _3231_onOwned = _out1491;
            _3232_recIdents = _out1492;
            if ((_3226_isDatatype) || (_3227_isConstant)) {
              r = RAST.Expr.create_Call((_3230_onExpr).Sel(DCOMP.__default.escapeIdent(_3228_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1493;
              DCOMP._IOwnership _out1494;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1493, out _out1494);
              r = _out1493;
              resultingOwnership = _out1494;
            } else {
              Dafny.ISequence<Dafny.Rune> _3233_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3233_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3230_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3228_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1495;
              DCOMP._IOwnership _out1496;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3233_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1495, out _out1496);
              r = _out1495;
              resultingOwnership = _out1496;
            }
            readIdents = _3232_recIdents;
            return ;
          }
        } else if (_source148.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3234___mcc_h98 = _source148.dtor_mapElems;
          bool _3235_isDatatype = _3115___mcc_h51;
          bool _3236_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3237_field = _3113___mcc_h49;
          DAST._IExpression _3238_on = _3112___mcc_h48;
          {
            RAST._IExpr _3239_onExpr;
            DCOMP._IOwnership _3240_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3241_recIdents;
            RAST._IExpr _out1497;
            DCOMP._IOwnership _out1498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1499;
            (this).GenExpr(_3238_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1497, out _out1498, out _out1499);
            _3239_onExpr = _out1497;
            _3240_onOwned = _out1498;
            _3241_recIdents = _out1499;
            if ((_3235_isDatatype) || (_3236_isConstant)) {
              r = RAST.Expr.create_Call((_3239_onExpr).Sel(DCOMP.__default.escapeIdent(_3237_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1500;
              DCOMP._IOwnership _out1501;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1500, out _out1501);
              r = _out1500;
              resultingOwnership = _out1501;
            } else {
              Dafny.ISequence<Dafny.Rune> _3242_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3242_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3239_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3237_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1502;
              DCOMP._IOwnership _out1503;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3242_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1502, out _out1503);
              r = _out1502;
              resultingOwnership = _out1503;
            }
            readIdents = _3241_recIdents;
            return ;
          }
        } else if (_source148.is_MapBuilder) {
          DAST._IType _3243___mcc_h100 = _source148.dtor_keyType;
          DAST._IType _3244___mcc_h101 = _source148.dtor_valueType;
          bool _3245_isDatatype = _3115___mcc_h51;
          bool _3246_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3247_field = _3113___mcc_h49;
          DAST._IExpression _3248_on = _3112___mcc_h48;
          {
            RAST._IExpr _3249_onExpr;
            DCOMP._IOwnership _3250_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3251_recIdents;
            RAST._IExpr _out1504;
            DCOMP._IOwnership _out1505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1506;
            (this).GenExpr(_3248_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1504, out _out1505, out _out1506);
            _3249_onExpr = _out1504;
            _3250_onOwned = _out1505;
            _3251_recIdents = _out1506;
            if ((_3245_isDatatype) || (_3246_isConstant)) {
              r = RAST.Expr.create_Call((_3249_onExpr).Sel(DCOMP.__default.escapeIdent(_3247_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1507;
              DCOMP._IOwnership _out1508;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1507, out _out1508);
              r = _out1507;
              resultingOwnership = _out1508;
            } else {
              Dafny.ISequence<Dafny.Rune> _3252_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3252_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3249_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3247_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1509;
              DCOMP._IOwnership _out1510;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3252_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1509, out _out1510);
              r = _out1509;
              resultingOwnership = _out1510;
            }
            readIdents = _3251_recIdents;
            return ;
          }
        } else if (_source148.is_SeqUpdate) {
          DAST._IExpression _3253___mcc_h104 = _source148.dtor_expr;
          DAST._IExpression _3254___mcc_h105 = _source148.dtor_indexExpr;
          DAST._IExpression _3255___mcc_h106 = _source148.dtor_value;
          bool _3256_isDatatype = _3115___mcc_h51;
          bool _3257_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3258_field = _3113___mcc_h49;
          DAST._IExpression _3259_on = _3112___mcc_h48;
          {
            RAST._IExpr _3260_onExpr;
            DCOMP._IOwnership _3261_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3262_recIdents;
            RAST._IExpr _out1511;
            DCOMP._IOwnership _out1512;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1513;
            (this).GenExpr(_3259_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1511, out _out1512, out _out1513);
            _3260_onExpr = _out1511;
            _3261_onOwned = _out1512;
            _3262_recIdents = _out1513;
            if ((_3256_isDatatype) || (_3257_isConstant)) {
              r = RAST.Expr.create_Call((_3260_onExpr).Sel(DCOMP.__default.escapeIdent(_3258_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1514;
              DCOMP._IOwnership _out1515;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1514, out _out1515);
              r = _out1514;
              resultingOwnership = _out1515;
            } else {
              Dafny.ISequence<Dafny.Rune> _3263_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3263_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3260_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3258_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1516;
              DCOMP._IOwnership _out1517;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3263_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1516, out _out1517);
              r = _out1516;
              resultingOwnership = _out1517;
            }
            readIdents = _3262_recIdents;
            return ;
          }
        } else if (_source148.is_MapUpdate) {
          DAST._IExpression _3264___mcc_h110 = _source148.dtor_expr;
          DAST._IExpression _3265___mcc_h111 = _source148.dtor_indexExpr;
          DAST._IExpression _3266___mcc_h112 = _source148.dtor_value;
          bool _3267_isDatatype = _3115___mcc_h51;
          bool _3268_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3269_field = _3113___mcc_h49;
          DAST._IExpression _3270_on = _3112___mcc_h48;
          {
            RAST._IExpr _3271_onExpr;
            DCOMP._IOwnership _3272_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3273_recIdents;
            RAST._IExpr _out1518;
            DCOMP._IOwnership _out1519;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1520;
            (this).GenExpr(_3270_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1518, out _out1519, out _out1520);
            _3271_onExpr = _out1518;
            _3272_onOwned = _out1519;
            _3273_recIdents = _out1520;
            if ((_3267_isDatatype) || (_3268_isConstant)) {
              r = RAST.Expr.create_Call((_3271_onExpr).Sel(DCOMP.__default.escapeIdent(_3269_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1521;
              DCOMP._IOwnership _out1522;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1521, out _out1522);
              r = _out1521;
              resultingOwnership = _out1522;
            } else {
              Dafny.ISequence<Dafny.Rune> _3274_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3274_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3271_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3269_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1523;
              DCOMP._IOwnership _out1524;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3274_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1523, out _out1524);
              r = _out1523;
              resultingOwnership = _out1524;
            }
            readIdents = _3273_recIdents;
            return ;
          }
        } else if (_source148.is_SetBuilder) {
          DAST._IType _3275___mcc_h116 = _source148.dtor_elemType;
          bool _3276_isDatatype = _3115___mcc_h51;
          bool _3277_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3278_field = _3113___mcc_h49;
          DAST._IExpression _3279_on = _3112___mcc_h48;
          {
            RAST._IExpr _3280_onExpr;
            DCOMP._IOwnership _3281_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3282_recIdents;
            RAST._IExpr _out1525;
            DCOMP._IOwnership _out1526;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1527;
            (this).GenExpr(_3279_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1525, out _out1526, out _out1527);
            _3280_onExpr = _out1525;
            _3281_onOwned = _out1526;
            _3282_recIdents = _out1527;
            if ((_3276_isDatatype) || (_3277_isConstant)) {
              r = RAST.Expr.create_Call((_3280_onExpr).Sel(DCOMP.__default.escapeIdent(_3278_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1528;
              DCOMP._IOwnership _out1529;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1528, out _out1529);
              r = _out1528;
              resultingOwnership = _out1529;
            } else {
              Dafny.ISequence<Dafny.Rune> _3283_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3283_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3280_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3278_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1530;
              DCOMP._IOwnership _out1531;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3283_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1530, out _out1531);
              r = _out1530;
              resultingOwnership = _out1531;
            }
            readIdents = _3282_recIdents;
            return ;
          }
        } else if (_source148.is_ToMultiset) {
          DAST._IExpression _3284___mcc_h118 = _source148.dtor_ToMultiset_a0;
          bool _3285_isDatatype = _3115___mcc_h51;
          bool _3286_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3287_field = _3113___mcc_h49;
          DAST._IExpression _3288_on = _3112___mcc_h48;
          {
            RAST._IExpr _3289_onExpr;
            DCOMP._IOwnership _3290_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3291_recIdents;
            RAST._IExpr _out1532;
            DCOMP._IOwnership _out1533;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1534;
            (this).GenExpr(_3288_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1532, out _out1533, out _out1534);
            _3289_onExpr = _out1532;
            _3290_onOwned = _out1533;
            _3291_recIdents = _out1534;
            if ((_3285_isDatatype) || (_3286_isConstant)) {
              r = RAST.Expr.create_Call((_3289_onExpr).Sel(DCOMP.__default.escapeIdent(_3287_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1535;
              DCOMP._IOwnership _out1536;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1535, out _out1536);
              r = _out1535;
              resultingOwnership = _out1536;
            } else {
              Dafny.ISequence<Dafny.Rune> _3292_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3292_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3289_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3287_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1537;
              DCOMP._IOwnership _out1538;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3292_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1537, out _out1538);
              r = _out1537;
              resultingOwnership = _out1538;
            }
            readIdents = _3291_recIdents;
            return ;
          }
        } else if (_source148.is_This) {
          bool _3293_isDatatype = _3115___mcc_h51;
          bool _3294_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3295_field = _3113___mcc_h49;
          DAST._IExpression _3296_on = _3112___mcc_h48;
          {
            RAST._IExpr _3297_onExpr;
            DCOMP._IOwnership _3298_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3299_recIdents;
            RAST._IExpr _out1539;
            DCOMP._IOwnership _out1540;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1541;
            (this).GenExpr(_3296_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1539, out _out1540, out _out1541);
            _3297_onExpr = _out1539;
            _3298_onOwned = _out1540;
            _3299_recIdents = _out1541;
            if ((_3293_isDatatype) || (_3294_isConstant)) {
              r = RAST.Expr.create_Call((_3297_onExpr).Sel(DCOMP.__default.escapeIdent(_3295_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1542;
              DCOMP._IOwnership _out1543;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1542, out _out1543);
              r = _out1542;
              resultingOwnership = _out1543;
            } else {
              Dafny.ISequence<Dafny.Rune> _3300_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3300_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3297_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3295_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1544;
              DCOMP._IOwnership _out1545;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3300_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1544, out _out1545);
              r = _out1544;
              resultingOwnership = _out1545;
            }
            readIdents = _3299_recIdents;
            return ;
          }
        } else if (_source148.is_Ite) {
          DAST._IExpression _3301___mcc_h120 = _source148.dtor_cond;
          DAST._IExpression _3302___mcc_h121 = _source148.dtor_thn;
          DAST._IExpression _3303___mcc_h122 = _source148.dtor_els;
          bool _3304_isDatatype = _3115___mcc_h51;
          bool _3305_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3306_field = _3113___mcc_h49;
          DAST._IExpression _3307_on = _3112___mcc_h48;
          {
            RAST._IExpr _3308_onExpr;
            DCOMP._IOwnership _3309_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3310_recIdents;
            RAST._IExpr _out1546;
            DCOMP._IOwnership _out1547;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1548;
            (this).GenExpr(_3307_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1546, out _out1547, out _out1548);
            _3308_onExpr = _out1546;
            _3309_onOwned = _out1547;
            _3310_recIdents = _out1548;
            if ((_3304_isDatatype) || (_3305_isConstant)) {
              r = RAST.Expr.create_Call((_3308_onExpr).Sel(DCOMP.__default.escapeIdent(_3306_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1549;
              DCOMP._IOwnership _out1550;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1549, out _out1550);
              r = _out1549;
              resultingOwnership = _out1550;
            } else {
              Dafny.ISequence<Dafny.Rune> _3311_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3311_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3308_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3306_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1551;
              DCOMP._IOwnership _out1552;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3311_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1551, out _out1552);
              r = _out1551;
              resultingOwnership = _out1552;
            }
            readIdents = _3310_recIdents;
            return ;
          }
        } else if (_source148.is_UnOp) {
          DAST._IUnaryOp _3312___mcc_h126 = _source148.dtor_unOp;
          DAST._IExpression _3313___mcc_h127 = _source148.dtor_expr;
          DAST.Format._IUnaryOpFormat _3314___mcc_h128 = _source148.dtor_format1;
          bool _3315_isDatatype = _3115___mcc_h51;
          bool _3316_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3317_field = _3113___mcc_h49;
          DAST._IExpression _3318_on = _3112___mcc_h48;
          {
            RAST._IExpr _3319_onExpr;
            DCOMP._IOwnership _3320_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3321_recIdents;
            RAST._IExpr _out1553;
            DCOMP._IOwnership _out1554;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1555;
            (this).GenExpr(_3318_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1553, out _out1554, out _out1555);
            _3319_onExpr = _out1553;
            _3320_onOwned = _out1554;
            _3321_recIdents = _out1555;
            if ((_3315_isDatatype) || (_3316_isConstant)) {
              r = RAST.Expr.create_Call((_3319_onExpr).Sel(DCOMP.__default.escapeIdent(_3317_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1556;
              DCOMP._IOwnership _out1557;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1556, out _out1557);
              r = _out1556;
              resultingOwnership = _out1557;
            } else {
              Dafny.ISequence<Dafny.Rune> _3322_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3322_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3319_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3317_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1558;
              DCOMP._IOwnership _out1559;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3322_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1558, out _out1559);
              r = _out1558;
              resultingOwnership = _out1559;
            }
            readIdents = _3321_recIdents;
            return ;
          }
        } else if (_source148.is_BinOp) {
          DAST._IBinOp _3323___mcc_h132 = _source148.dtor_op;
          DAST._IExpression _3324___mcc_h133 = _source148.dtor_left;
          DAST._IExpression _3325___mcc_h134 = _source148.dtor_right;
          DAST.Format._IBinaryOpFormat _3326___mcc_h135 = _source148.dtor_format2;
          bool _3327_isDatatype = _3115___mcc_h51;
          bool _3328_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3329_field = _3113___mcc_h49;
          DAST._IExpression _3330_on = _3112___mcc_h48;
          {
            RAST._IExpr _3331_onExpr;
            DCOMP._IOwnership _3332_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3333_recIdents;
            RAST._IExpr _out1560;
            DCOMP._IOwnership _out1561;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1562;
            (this).GenExpr(_3330_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1560, out _out1561, out _out1562);
            _3331_onExpr = _out1560;
            _3332_onOwned = _out1561;
            _3333_recIdents = _out1562;
            if ((_3327_isDatatype) || (_3328_isConstant)) {
              r = RAST.Expr.create_Call((_3331_onExpr).Sel(DCOMP.__default.escapeIdent(_3329_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1563;
              DCOMP._IOwnership _out1564;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1563, out _out1564);
              r = _out1563;
              resultingOwnership = _out1564;
            } else {
              Dafny.ISequence<Dafny.Rune> _3334_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3334_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3331_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3329_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1565;
              DCOMP._IOwnership _out1566;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3334_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1565, out _out1566);
              r = _out1565;
              resultingOwnership = _out1566;
            }
            readIdents = _3333_recIdents;
            return ;
          }
        } else if (_source148.is_ArrayLen) {
          DAST._IExpression _3335___mcc_h140 = _source148.dtor_expr;
          BigInteger _3336___mcc_h141 = _source148.dtor_dim;
          bool _3337_isDatatype = _3115___mcc_h51;
          bool _3338_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3339_field = _3113___mcc_h49;
          DAST._IExpression _3340_on = _3112___mcc_h48;
          {
            RAST._IExpr _3341_onExpr;
            DCOMP._IOwnership _3342_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3343_recIdents;
            RAST._IExpr _out1567;
            DCOMP._IOwnership _out1568;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1569;
            (this).GenExpr(_3340_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1567, out _out1568, out _out1569);
            _3341_onExpr = _out1567;
            _3342_onOwned = _out1568;
            _3343_recIdents = _out1569;
            if ((_3337_isDatatype) || (_3338_isConstant)) {
              r = RAST.Expr.create_Call((_3341_onExpr).Sel(DCOMP.__default.escapeIdent(_3339_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1570;
              DCOMP._IOwnership _out1571;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1570, out _out1571);
              r = _out1570;
              resultingOwnership = _out1571;
            } else {
              Dafny.ISequence<Dafny.Rune> _3344_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3344_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3341_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3339_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1572;
              DCOMP._IOwnership _out1573;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3344_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1572, out _out1573);
              r = _out1572;
              resultingOwnership = _out1573;
            }
            readIdents = _3343_recIdents;
            return ;
          }
        } else if (_source148.is_MapKeys) {
          DAST._IExpression _3345___mcc_h144 = _source148.dtor_expr;
          bool _3346_isDatatype = _3115___mcc_h51;
          bool _3347_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3348_field = _3113___mcc_h49;
          DAST._IExpression _3349_on = _3112___mcc_h48;
          {
            RAST._IExpr _3350_onExpr;
            DCOMP._IOwnership _3351_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3352_recIdents;
            RAST._IExpr _out1574;
            DCOMP._IOwnership _out1575;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1576;
            (this).GenExpr(_3349_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1574, out _out1575, out _out1576);
            _3350_onExpr = _out1574;
            _3351_onOwned = _out1575;
            _3352_recIdents = _out1576;
            if ((_3346_isDatatype) || (_3347_isConstant)) {
              r = RAST.Expr.create_Call((_3350_onExpr).Sel(DCOMP.__default.escapeIdent(_3348_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1577;
              DCOMP._IOwnership _out1578;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1577, out _out1578);
              r = _out1577;
              resultingOwnership = _out1578;
            } else {
              Dafny.ISequence<Dafny.Rune> _3353_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3353_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3350_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3348_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1579;
              DCOMP._IOwnership _out1580;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3353_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1579, out _out1580);
              r = _out1579;
              resultingOwnership = _out1580;
            }
            readIdents = _3352_recIdents;
            return ;
          }
        } else if (_source148.is_MapValues) {
          DAST._IExpression _3354___mcc_h146 = _source148.dtor_expr;
          bool _3355_isDatatype = _3115___mcc_h51;
          bool _3356_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3357_field = _3113___mcc_h49;
          DAST._IExpression _3358_on = _3112___mcc_h48;
          {
            RAST._IExpr _3359_onExpr;
            DCOMP._IOwnership _3360_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3361_recIdents;
            RAST._IExpr _out1581;
            DCOMP._IOwnership _out1582;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1583;
            (this).GenExpr(_3358_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1581, out _out1582, out _out1583);
            _3359_onExpr = _out1581;
            _3360_onOwned = _out1582;
            _3361_recIdents = _out1583;
            if ((_3355_isDatatype) || (_3356_isConstant)) {
              r = RAST.Expr.create_Call((_3359_onExpr).Sel(DCOMP.__default.escapeIdent(_3357_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1584;
              DCOMP._IOwnership _out1585;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1584, out _out1585);
              r = _out1584;
              resultingOwnership = _out1585;
            } else {
              Dafny.ISequence<Dafny.Rune> _3362_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3362_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3359_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3357_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1586;
              DCOMP._IOwnership _out1587;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3362_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1586, out _out1587);
              r = _out1586;
              resultingOwnership = _out1587;
            }
            readIdents = _3361_recIdents;
            return ;
          }
        } else if (_source148.is_Select) {
          DAST._IExpression _3363___mcc_h148 = _source148.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _3364___mcc_h149 = _source148.dtor_field;
          bool _3365___mcc_h150 = _source148.dtor_isConstant;
          bool _3366___mcc_h151 = _source148.dtor_onDatatype;
          bool _3367_isDatatype = _3115___mcc_h51;
          bool _3368_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3369_field = _3113___mcc_h49;
          DAST._IExpression _3370_on = _3112___mcc_h48;
          {
            RAST._IExpr _3371_onExpr;
            DCOMP._IOwnership _3372_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3373_recIdents;
            RAST._IExpr _out1588;
            DCOMP._IOwnership _out1589;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1590;
            (this).GenExpr(_3370_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1588, out _out1589, out _out1590);
            _3371_onExpr = _out1588;
            _3372_onOwned = _out1589;
            _3373_recIdents = _out1590;
            if ((_3367_isDatatype) || (_3368_isConstant)) {
              r = RAST.Expr.create_Call((_3371_onExpr).Sel(DCOMP.__default.escapeIdent(_3369_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1591;
              DCOMP._IOwnership _out1592;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1591, out _out1592);
              r = _out1591;
              resultingOwnership = _out1592;
            } else {
              Dafny.ISequence<Dafny.Rune> _3374_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3374_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3371_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3369_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1593;
              DCOMP._IOwnership _out1594;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3374_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1593, out _out1594);
              r = _out1593;
              resultingOwnership = _out1594;
            }
            readIdents = _3373_recIdents;
            return ;
          }
        } else if (_source148.is_SelectFn) {
          DAST._IExpression _3375___mcc_h156 = _source148.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _3376___mcc_h157 = _source148.dtor_field;
          bool _3377___mcc_h158 = _source148.dtor_onDatatype;
          bool _3378___mcc_h159 = _source148.dtor_isStatic;
          BigInteger _3379___mcc_h160 = _source148.dtor_arity;
          bool _3380_isDatatype = _3115___mcc_h51;
          bool _3381_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3382_field = _3113___mcc_h49;
          DAST._IExpression _3383_on = _3112___mcc_h48;
          {
            RAST._IExpr _3384_onExpr;
            DCOMP._IOwnership _3385_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3386_recIdents;
            RAST._IExpr _out1595;
            DCOMP._IOwnership _out1596;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1597;
            (this).GenExpr(_3383_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1595, out _out1596, out _out1597);
            _3384_onExpr = _out1595;
            _3385_onOwned = _out1596;
            _3386_recIdents = _out1597;
            if ((_3380_isDatatype) || (_3381_isConstant)) {
              r = RAST.Expr.create_Call((_3384_onExpr).Sel(DCOMP.__default.escapeIdent(_3382_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1598;
              DCOMP._IOwnership _out1599;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1598, out _out1599);
              r = _out1598;
              resultingOwnership = _out1599;
            } else {
              Dafny.ISequence<Dafny.Rune> _3387_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3387_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3384_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3382_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1600;
              DCOMP._IOwnership _out1601;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3387_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1600, out _out1601);
              r = _out1600;
              resultingOwnership = _out1601;
            }
            readIdents = _3386_recIdents;
            return ;
          }
        } else if (_source148.is_Index) {
          DAST._IExpression _3388___mcc_h166 = _source148.dtor_expr;
          DAST._ICollKind _3389___mcc_h167 = _source148.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _3390___mcc_h168 = _source148.dtor_indices;
          bool _3391_isDatatype = _3115___mcc_h51;
          bool _3392_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3393_field = _3113___mcc_h49;
          DAST._IExpression _3394_on = _3112___mcc_h48;
          {
            RAST._IExpr _3395_onExpr;
            DCOMP._IOwnership _3396_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3397_recIdents;
            RAST._IExpr _out1602;
            DCOMP._IOwnership _out1603;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1604;
            (this).GenExpr(_3394_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1602, out _out1603, out _out1604);
            _3395_onExpr = _out1602;
            _3396_onOwned = _out1603;
            _3397_recIdents = _out1604;
            if ((_3391_isDatatype) || (_3392_isConstant)) {
              r = RAST.Expr.create_Call((_3395_onExpr).Sel(DCOMP.__default.escapeIdent(_3393_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1605;
              DCOMP._IOwnership _out1606;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1605, out _out1606);
              r = _out1605;
              resultingOwnership = _out1606;
            } else {
              Dafny.ISequence<Dafny.Rune> _3398_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3398_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3395_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3393_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1607;
              DCOMP._IOwnership _out1608;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3398_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1607, out _out1608);
              r = _out1607;
              resultingOwnership = _out1608;
            }
            readIdents = _3397_recIdents;
            return ;
          }
        } else if (_source148.is_IndexRange) {
          DAST._IExpression _3399___mcc_h172 = _source148.dtor_expr;
          bool _3400___mcc_h173 = _source148.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _3401___mcc_h174 = _source148.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _3402___mcc_h175 = _source148.dtor_high;
          bool _3403_isDatatype = _3115___mcc_h51;
          bool _3404_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3405_field = _3113___mcc_h49;
          DAST._IExpression _3406_on = _3112___mcc_h48;
          {
            RAST._IExpr _3407_onExpr;
            DCOMP._IOwnership _3408_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3409_recIdents;
            RAST._IExpr _out1609;
            DCOMP._IOwnership _out1610;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1611;
            (this).GenExpr(_3406_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1609, out _out1610, out _out1611);
            _3407_onExpr = _out1609;
            _3408_onOwned = _out1610;
            _3409_recIdents = _out1611;
            if ((_3403_isDatatype) || (_3404_isConstant)) {
              r = RAST.Expr.create_Call((_3407_onExpr).Sel(DCOMP.__default.escapeIdent(_3405_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1612;
              DCOMP._IOwnership _out1613;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1612, out _out1613);
              r = _out1612;
              resultingOwnership = _out1613;
            } else {
              Dafny.ISequence<Dafny.Rune> _3410_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3410_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3407_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3405_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1614;
              DCOMP._IOwnership _out1615;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3410_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1614, out _out1615);
              r = _out1614;
              resultingOwnership = _out1615;
            }
            readIdents = _3409_recIdents;
            return ;
          }
        } else if (_source148.is_TupleSelect) {
          DAST._IExpression _3411___mcc_h180 = _source148.dtor_expr;
          BigInteger _3412___mcc_h181 = _source148.dtor_index;
          bool _3413_isDatatype = _3115___mcc_h51;
          bool _3414_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3415_field = _3113___mcc_h49;
          DAST._IExpression _3416_on = _3112___mcc_h48;
          {
            RAST._IExpr _3417_onExpr;
            DCOMP._IOwnership _3418_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3419_recIdents;
            RAST._IExpr _out1616;
            DCOMP._IOwnership _out1617;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1618;
            (this).GenExpr(_3416_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1616, out _out1617, out _out1618);
            _3417_onExpr = _out1616;
            _3418_onOwned = _out1617;
            _3419_recIdents = _out1618;
            if ((_3413_isDatatype) || (_3414_isConstant)) {
              r = RAST.Expr.create_Call((_3417_onExpr).Sel(DCOMP.__default.escapeIdent(_3415_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1619;
              DCOMP._IOwnership _out1620;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1619, out _out1620);
              r = _out1619;
              resultingOwnership = _out1620;
            } else {
              Dafny.ISequence<Dafny.Rune> _3420_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3420_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3417_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3415_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1621;
              DCOMP._IOwnership _out1622;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3420_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1621, out _out1622);
              r = _out1621;
              resultingOwnership = _out1622;
            }
            readIdents = _3419_recIdents;
            return ;
          }
        } else if (_source148.is_Call) {
          DAST._IExpression _3421___mcc_h184 = _source148.dtor_on;
          DAST._ICallName _3422___mcc_h185 = _source148.dtor_callName;
          Dafny.ISequence<DAST._IType> _3423___mcc_h186 = _source148.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _3424___mcc_h187 = _source148.dtor_args;
          bool _3425_isDatatype = _3115___mcc_h51;
          bool _3426_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3427_field = _3113___mcc_h49;
          DAST._IExpression _3428_on = _3112___mcc_h48;
          {
            RAST._IExpr _3429_onExpr;
            DCOMP._IOwnership _3430_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3431_recIdents;
            RAST._IExpr _out1623;
            DCOMP._IOwnership _out1624;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1625;
            (this).GenExpr(_3428_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1623, out _out1624, out _out1625);
            _3429_onExpr = _out1623;
            _3430_onOwned = _out1624;
            _3431_recIdents = _out1625;
            if ((_3425_isDatatype) || (_3426_isConstant)) {
              r = RAST.Expr.create_Call((_3429_onExpr).Sel(DCOMP.__default.escapeIdent(_3427_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1626;
              DCOMP._IOwnership _out1627;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1626, out _out1627);
              r = _out1626;
              resultingOwnership = _out1627;
            } else {
              Dafny.ISequence<Dafny.Rune> _3432_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3432_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3429_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3427_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1628;
              DCOMP._IOwnership _out1629;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3432_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1628, out _out1629);
              r = _out1628;
              resultingOwnership = _out1629;
            }
            readIdents = _3431_recIdents;
            return ;
          }
        } else if (_source148.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _3433___mcc_h192 = _source148.dtor_params;
          DAST._IType _3434___mcc_h193 = _source148.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _3435___mcc_h194 = _source148.dtor_body;
          bool _3436_isDatatype = _3115___mcc_h51;
          bool _3437_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3438_field = _3113___mcc_h49;
          DAST._IExpression _3439_on = _3112___mcc_h48;
          {
            RAST._IExpr _3440_onExpr;
            DCOMP._IOwnership _3441_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3442_recIdents;
            RAST._IExpr _out1630;
            DCOMP._IOwnership _out1631;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1632;
            (this).GenExpr(_3439_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1630, out _out1631, out _out1632);
            _3440_onExpr = _out1630;
            _3441_onOwned = _out1631;
            _3442_recIdents = _out1632;
            if ((_3436_isDatatype) || (_3437_isConstant)) {
              r = RAST.Expr.create_Call((_3440_onExpr).Sel(DCOMP.__default.escapeIdent(_3438_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1633;
              DCOMP._IOwnership _out1634;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1633, out _out1634);
              r = _out1633;
              resultingOwnership = _out1634;
            } else {
              Dafny.ISequence<Dafny.Rune> _3443_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3443_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3440_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3438_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1635;
              DCOMP._IOwnership _out1636;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3443_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1635, out _out1636);
              r = _out1635;
              resultingOwnership = _out1636;
            }
            readIdents = _3442_recIdents;
            return ;
          }
        } else if (_source148.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _3444___mcc_h198 = _source148.dtor_values;
          DAST._IType _3445___mcc_h199 = _source148.dtor_retType;
          DAST._IExpression _3446___mcc_h200 = _source148.dtor_expr;
          bool _3447_isDatatype = _3115___mcc_h51;
          bool _3448_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3449_field = _3113___mcc_h49;
          DAST._IExpression _3450_on = _3112___mcc_h48;
          {
            RAST._IExpr _3451_onExpr;
            DCOMP._IOwnership _3452_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3453_recIdents;
            RAST._IExpr _out1637;
            DCOMP._IOwnership _out1638;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1639;
            (this).GenExpr(_3450_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1637, out _out1638, out _out1639);
            _3451_onExpr = _out1637;
            _3452_onOwned = _out1638;
            _3453_recIdents = _out1639;
            if ((_3447_isDatatype) || (_3448_isConstant)) {
              r = RAST.Expr.create_Call((_3451_onExpr).Sel(DCOMP.__default.escapeIdent(_3449_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1640;
              DCOMP._IOwnership _out1641;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1640, out _out1641);
              r = _out1640;
              resultingOwnership = _out1641;
            } else {
              Dafny.ISequence<Dafny.Rune> _3454_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3454_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3451_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3449_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1642;
              DCOMP._IOwnership _out1643;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3454_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1642, out _out1643);
              r = _out1642;
              resultingOwnership = _out1643;
            }
            readIdents = _3453_recIdents;
            return ;
          }
        } else if (_source148.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _3455___mcc_h204 = _source148.dtor_name;
          DAST._IType _3456___mcc_h205 = _source148.dtor_typ;
          DAST._IExpression _3457___mcc_h206 = _source148.dtor_value;
          DAST._IExpression _3458___mcc_h207 = _source148.dtor_iifeBody;
          bool _3459_isDatatype = _3115___mcc_h51;
          bool _3460_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3461_field = _3113___mcc_h49;
          DAST._IExpression _3462_on = _3112___mcc_h48;
          {
            RAST._IExpr _3463_onExpr;
            DCOMP._IOwnership _3464_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3465_recIdents;
            RAST._IExpr _out1644;
            DCOMP._IOwnership _out1645;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1646;
            (this).GenExpr(_3462_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1644, out _out1645, out _out1646);
            _3463_onExpr = _out1644;
            _3464_onOwned = _out1645;
            _3465_recIdents = _out1646;
            if ((_3459_isDatatype) || (_3460_isConstant)) {
              r = RAST.Expr.create_Call((_3463_onExpr).Sel(DCOMP.__default.escapeIdent(_3461_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1647;
              DCOMP._IOwnership _out1648;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1647, out _out1648);
              r = _out1647;
              resultingOwnership = _out1648;
            } else {
              Dafny.ISequence<Dafny.Rune> _3466_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3466_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3463_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3461_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1649;
              DCOMP._IOwnership _out1650;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3466_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1649, out _out1650);
              r = _out1649;
              resultingOwnership = _out1650;
            }
            readIdents = _3465_recIdents;
            return ;
          }
        } else if (_source148.is_Apply) {
          DAST._IExpression _3467___mcc_h212 = _source148.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _3468___mcc_h213 = _source148.dtor_args;
          bool _3469_isDatatype = _3115___mcc_h51;
          bool _3470_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3471_field = _3113___mcc_h49;
          DAST._IExpression _3472_on = _3112___mcc_h48;
          {
            RAST._IExpr _3473_onExpr;
            DCOMP._IOwnership _3474_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3475_recIdents;
            RAST._IExpr _out1651;
            DCOMP._IOwnership _out1652;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1653;
            (this).GenExpr(_3472_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1651, out _out1652, out _out1653);
            _3473_onExpr = _out1651;
            _3474_onOwned = _out1652;
            _3475_recIdents = _out1653;
            if ((_3469_isDatatype) || (_3470_isConstant)) {
              r = RAST.Expr.create_Call((_3473_onExpr).Sel(DCOMP.__default.escapeIdent(_3471_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1654;
              DCOMP._IOwnership _out1655;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1654, out _out1655);
              r = _out1654;
              resultingOwnership = _out1655;
            } else {
              Dafny.ISequence<Dafny.Rune> _3476_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3476_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3473_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3471_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1656;
              DCOMP._IOwnership _out1657;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3476_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1656, out _out1657);
              r = _out1656;
              resultingOwnership = _out1657;
            }
            readIdents = _3475_recIdents;
            return ;
          }
        } else if (_source148.is_TypeTest) {
          DAST._IExpression _3477___mcc_h216 = _source148.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3478___mcc_h217 = _source148.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _3479___mcc_h218 = _source148.dtor_variant;
          bool _3480_isDatatype = _3115___mcc_h51;
          bool _3481_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3482_field = _3113___mcc_h49;
          DAST._IExpression _3483_on = _3112___mcc_h48;
          {
            RAST._IExpr _3484_onExpr;
            DCOMP._IOwnership _3485_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3486_recIdents;
            RAST._IExpr _out1658;
            DCOMP._IOwnership _out1659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1660;
            (this).GenExpr(_3483_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1658, out _out1659, out _out1660);
            _3484_onExpr = _out1658;
            _3485_onOwned = _out1659;
            _3486_recIdents = _out1660;
            if ((_3480_isDatatype) || (_3481_isConstant)) {
              r = RAST.Expr.create_Call((_3484_onExpr).Sel(DCOMP.__default.escapeIdent(_3482_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1661;
              DCOMP._IOwnership _out1662;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1661, out _out1662);
              r = _out1661;
              resultingOwnership = _out1662;
            } else {
              Dafny.ISequence<Dafny.Rune> _3487_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3487_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3484_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3482_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1663;
              DCOMP._IOwnership _out1664;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3487_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1663, out _out1664);
              r = _out1663;
              resultingOwnership = _out1664;
            }
            readIdents = _3486_recIdents;
            return ;
          }
        } else if (_source148.is_InitializationValue) {
          DAST._IType _3488___mcc_h222 = _source148.dtor_typ;
          bool _3489_isDatatype = _3115___mcc_h51;
          bool _3490_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3491_field = _3113___mcc_h49;
          DAST._IExpression _3492_on = _3112___mcc_h48;
          {
            RAST._IExpr _3493_onExpr;
            DCOMP._IOwnership _3494_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3495_recIdents;
            RAST._IExpr _out1665;
            DCOMP._IOwnership _out1666;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1667;
            (this).GenExpr(_3492_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1665, out _out1666, out _out1667);
            _3493_onExpr = _out1665;
            _3494_onOwned = _out1666;
            _3495_recIdents = _out1667;
            if ((_3489_isDatatype) || (_3490_isConstant)) {
              r = RAST.Expr.create_Call((_3493_onExpr).Sel(DCOMP.__default.escapeIdent(_3491_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1668;
              DCOMP._IOwnership _out1669;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1668, out _out1669);
              r = _out1668;
              resultingOwnership = _out1669;
            } else {
              Dafny.ISequence<Dafny.Rune> _3496_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3496_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3493_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3491_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1670;
              DCOMP._IOwnership _out1671;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3496_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1670, out _out1671);
              r = _out1670;
              resultingOwnership = _out1671;
            }
            readIdents = _3495_recIdents;
            return ;
          }
        } else if (_source148.is_BoolBoundedPool) {
          bool _3497_isDatatype = _3115___mcc_h51;
          bool _3498_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3499_field = _3113___mcc_h49;
          DAST._IExpression _3500_on = _3112___mcc_h48;
          {
            RAST._IExpr _3501_onExpr;
            DCOMP._IOwnership _3502_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3503_recIdents;
            RAST._IExpr _out1672;
            DCOMP._IOwnership _out1673;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1674;
            (this).GenExpr(_3500_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1672, out _out1673, out _out1674);
            _3501_onExpr = _out1672;
            _3502_onOwned = _out1673;
            _3503_recIdents = _out1674;
            if ((_3497_isDatatype) || (_3498_isConstant)) {
              r = RAST.Expr.create_Call((_3501_onExpr).Sel(DCOMP.__default.escapeIdent(_3499_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1675;
              DCOMP._IOwnership _out1676;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1675, out _out1676);
              r = _out1675;
              resultingOwnership = _out1676;
            } else {
              Dafny.ISequence<Dafny.Rune> _3504_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3504_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3501_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3499_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1677;
              DCOMP._IOwnership _out1678;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3504_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1677, out _out1678);
              r = _out1677;
              resultingOwnership = _out1678;
            }
            readIdents = _3503_recIdents;
            return ;
          }
        } else if (_source148.is_SetBoundedPool) {
          DAST._IExpression _3505___mcc_h224 = _source148.dtor_of;
          bool _3506_isDatatype = _3115___mcc_h51;
          bool _3507_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3508_field = _3113___mcc_h49;
          DAST._IExpression _3509_on = _3112___mcc_h48;
          {
            RAST._IExpr _3510_onExpr;
            DCOMP._IOwnership _3511_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3512_recIdents;
            RAST._IExpr _out1679;
            DCOMP._IOwnership _out1680;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1681;
            (this).GenExpr(_3509_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1679, out _out1680, out _out1681);
            _3510_onExpr = _out1679;
            _3511_onOwned = _out1680;
            _3512_recIdents = _out1681;
            if ((_3506_isDatatype) || (_3507_isConstant)) {
              r = RAST.Expr.create_Call((_3510_onExpr).Sel(DCOMP.__default.escapeIdent(_3508_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1682;
              DCOMP._IOwnership _out1683;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1682, out _out1683);
              r = _out1682;
              resultingOwnership = _out1683;
            } else {
              Dafny.ISequence<Dafny.Rune> _3513_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3513_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3510_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3508_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1684;
              DCOMP._IOwnership _out1685;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3513_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1684, out _out1685);
              r = _out1684;
              resultingOwnership = _out1685;
            }
            readIdents = _3512_recIdents;
            return ;
          }
        } else if (_source148.is_SeqBoundedPool) {
          DAST._IExpression _3514___mcc_h226 = _source148.dtor_of;
          bool _3515___mcc_h227 = _source148.dtor_includeDuplicates;
          bool _3516_isDatatype = _3115___mcc_h51;
          bool _3517_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3518_field = _3113___mcc_h49;
          DAST._IExpression _3519_on = _3112___mcc_h48;
          {
            RAST._IExpr _3520_onExpr;
            DCOMP._IOwnership _3521_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3522_recIdents;
            RAST._IExpr _out1686;
            DCOMP._IOwnership _out1687;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1688;
            (this).GenExpr(_3519_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1686, out _out1687, out _out1688);
            _3520_onExpr = _out1686;
            _3521_onOwned = _out1687;
            _3522_recIdents = _out1688;
            if ((_3516_isDatatype) || (_3517_isConstant)) {
              r = RAST.Expr.create_Call((_3520_onExpr).Sel(DCOMP.__default.escapeIdent(_3518_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1689;
              DCOMP._IOwnership _out1690;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1689, out _out1690);
              r = _out1689;
              resultingOwnership = _out1690;
            } else {
              Dafny.ISequence<Dafny.Rune> _3523_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3523_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3520_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3518_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1691;
              DCOMP._IOwnership _out1692;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3523_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1691, out _out1692);
              r = _out1691;
              resultingOwnership = _out1692;
            }
            readIdents = _3522_recIdents;
            return ;
          }
        } else {
          DAST._IExpression _3524___mcc_h230 = _source148.dtor_lo;
          DAST._IExpression _3525___mcc_h231 = _source148.dtor_hi;
          bool _3526_isDatatype = _3115___mcc_h51;
          bool _3527_isConstant = _3114___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _3528_field = _3113___mcc_h49;
          DAST._IExpression _3529_on = _3112___mcc_h48;
          {
            RAST._IExpr _3530_onExpr;
            DCOMP._IOwnership _3531_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3532_recIdents;
            RAST._IExpr _out1693;
            DCOMP._IOwnership _out1694;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1695;
            (this).GenExpr(_3529_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1693, out _out1694, out _out1695);
            _3530_onExpr = _out1693;
            _3531_onOwned = _out1694;
            _3532_recIdents = _out1695;
            if ((_3526_isDatatype) || (_3527_isConstant)) {
              r = RAST.Expr.create_Call((_3530_onExpr).Sel(DCOMP.__default.escapeIdent(_3528_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out1696;
              DCOMP._IOwnership _out1697;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1696, out _out1697);
              r = _out1696;
              resultingOwnership = _out1697;
            } else {
              Dafny.ISequence<Dafny.Rune> _3533_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _3533_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_3530_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_3528_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out1698;
              DCOMP._IOwnership _out1699;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_3533_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1698, out _out1699);
              r = _out1698;
              resultingOwnership = _out1699;
            }
            readIdents = _3532_recIdents;
            return ;
          }
        }
      } else if (_source145.is_SelectFn) {
        DAST._IExpression _3534___mcc_h234 = _source145.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _3535___mcc_h235 = _source145.dtor_field;
        bool _3536___mcc_h236 = _source145.dtor_onDatatype;
        bool _3537___mcc_h237 = _source145.dtor_isStatic;
        BigInteger _3538___mcc_h238 = _source145.dtor_arity;
        BigInteger _3539_arity = _3538___mcc_h238;
        bool _3540_isStatic = _3537___mcc_h237;
        bool _3541_isDatatype = _3536___mcc_h236;
        Dafny.ISequence<Dafny.Rune> _3542_field = _3535___mcc_h235;
        DAST._IExpression _3543_on = _3534___mcc_h234;
        {
          RAST._IExpr _3544_onExpr;
          DCOMP._IOwnership _3545_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3546_recIdents;
          RAST._IExpr _out1700;
          DCOMP._IOwnership _out1701;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1702;
          (this).GenExpr(_3543_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1700, out _out1701, out _out1702);
          _3544_onExpr = _out1700;
          _3545_onOwned = _out1701;
          _3546_recIdents = _out1702;
          Dafny.ISequence<Dafny.Rune> _3547_s = Dafny.Sequence<Dafny.Rune>.Empty;
          Dafny.ISequence<Dafny.Rune> _3548_onString;
          _3548_onString = (_3544_onExpr)._ToString(DCOMP.__default.IND);
          if (_3540_isStatic) {
            _3547_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3548_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_3542_field));
          } else {
            _3547_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            _3547_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3547_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _3548_onString), ((object.Equals(_3545_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _3549_args;
            _3549_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _3550_i;
            _3550_i = BigInteger.Zero;
            while ((_3550_i) < (_3539_arity)) {
              if ((_3550_i).Sign == 1) {
                _3549_args = Dafny.Sequence<Dafny.Rune>.Concat(_3549_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _3549_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3549_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_3550_i));
              _3550_i = (_3550_i) + (BigInteger.One);
            }
            _3547_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3547_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _3549_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            _3547_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3547_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _3542_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _3549_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            _3547_s = Dafny.Sequence<Dafny.Rune>.Concat(_3547_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _3547_s = Dafny.Sequence<Dafny.Rune>.Concat(_3547_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          Dafny.ISequence<Dafny.Rune> _3551_typeShape;
          _3551_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
          BigInteger _3552_i;
          _3552_i = BigInteger.Zero;
          while ((_3552_i) < (_3539_arity)) {
            if ((_3552_i).Sign == 1) {
              _3551_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_3551_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            _3551_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_3551_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
            _3552_i = (_3552_i) + (BigInteger.One);
          }
          _3551_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_3551_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
          _3547_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper(::std::rc::Rc::new("), _3547_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _3551_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">)"));
          r = RAST.Expr.create_RawExpr(_3547_s);
          RAST._IExpr _out1703;
          DCOMP._IOwnership _out1704;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1703, out _out1704);
          r = _out1703;
          resultingOwnership = _out1704;
          readIdents = _3546_recIdents;
          return ;
        }
      } else if (_source145.is_Index) {
        DAST._IExpression _3553___mcc_h239 = _source145.dtor_expr;
        DAST._ICollKind _3554___mcc_h240 = _source145.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _3555___mcc_h241 = _source145.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _3556_indices = _3555___mcc_h241;
        DAST._ICollKind _3557_collKind = _3554___mcc_h240;
        DAST._IExpression _3558_on = _3553___mcc_h239;
        {
          RAST._IExpr _3559_onExpr;
          DCOMP._IOwnership _3560_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3561_recIdents;
          RAST._IExpr _out1705;
          DCOMP._IOwnership _out1706;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1707;
          (this).GenExpr(_3558_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1705, out _out1706, out _out1707);
          _3559_onExpr = _out1705;
          _3560_onOwned = _out1706;
          _3561_recIdents = _out1707;
          readIdents = _3561_recIdents;
          r = _3559_onExpr;
          BigInteger _3562_i;
          _3562_i = BigInteger.Zero;
          while ((_3562_i) < (new BigInteger((_3556_indices).Count))) {
            if (object.Equals(_3557_collKind, DAST.CollKind.create_Array())) {
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IExpr _3563_idx;
            DCOMP._IOwnership _3564_idxOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3565_recIdentsIdx;
            RAST._IExpr _out1708;
            DCOMP._IOwnership _out1709;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1710;
            (this).GenExpr((_3556_indices).Select(_3562_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1708, out _out1709, out _out1710);
            _3563_idx = _out1708;
            _3564_idxOwned = _out1709;
            _3565_recIdentsIdx = _out1710;
            r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_3563_idx);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3565_recIdentsIdx);
            _3562_i = (_3562_i) + (BigInteger.One);
          }
          RAST._IExpr _out1711;
          DCOMP._IOwnership _out1712;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1711, out _out1712);
          r = _out1711;
          resultingOwnership = _out1712;
          return ;
        }
      } else if (_source145.is_IndexRange) {
        DAST._IExpression _3566___mcc_h242 = _source145.dtor_expr;
        bool _3567___mcc_h243 = _source145.dtor_isArray;
        Std.Wrappers._IOption<DAST._IExpression> _3568___mcc_h244 = _source145.dtor_low;
        Std.Wrappers._IOption<DAST._IExpression> _3569___mcc_h245 = _source145.dtor_high;
        Std.Wrappers._IOption<DAST._IExpression> _3570_high = _3569___mcc_h245;
        Std.Wrappers._IOption<DAST._IExpression> _3571_low = _3568___mcc_h244;
        bool _3572_isArray = _3567___mcc_h243;
        DAST._IExpression _3573_on = _3566___mcc_h242;
        {
          RAST._IExpr _3574_onExpr;
          DCOMP._IOwnership _3575_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3576_recIdents;
          RAST._IExpr _out1713;
          DCOMP._IOwnership _out1714;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1715;
          (this).GenExpr(_3573_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1713, out _out1714, out _out1715);
          _3574_onExpr = _out1713;
          _3575_onOwned = _out1714;
          _3576_recIdents = _out1715;
          readIdents = _3576_recIdents;
          Dafny.ISequence<Dafny.Rune> _3577_methodName;
          _3577_methodName = (((_3571_low).is_Some) ? ((((_3570_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_3570_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
          Dafny.ISequence<RAST._IExpr> _3578_arguments;
          _3578_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          Std.Wrappers._IOption<DAST._IExpression> _source149 = _3571_low;
          if (_source149.is_None) {
          } else {
            DAST._IExpression _3579___mcc_h274 = _source149.dtor_value;
            DAST._IExpression _3580_l = _3579___mcc_h274;
            {
              RAST._IExpr _3581_lExpr;
              DCOMP._IOwnership _3582___v115;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3583_recIdentsL;
              RAST._IExpr _out1716;
              DCOMP._IOwnership _out1717;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1718;
              (this).GenExpr(_3580_l, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1716, out _out1717, out _out1718);
              _3581_lExpr = _out1716;
              _3582___v115 = _out1717;
              _3583_recIdentsL = _out1718;
              _3578_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3578_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_3581_lExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3583_recIdentsL);
            }
          }
          Std.Wrappers._IOption<DAST._IExpression> _source150 = _3570_high;
          if (_source150.is_None) {
          } else {
            DAST._IExpression _3584___mcc_h275 = _source150.dtor_value;
            DAST._IExpression _3585_h = _3584___mcc_h275;
            {
              RAST._IExpr _3586_hExpr;
              DCOMP._IOwnership _3587___v116;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3588_recIdentsH;
              RAST._IExpr _out1719;
              DCOMP._IOwnership _out1720;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1721;
              (this).GenExpr(_3585_h, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1719, out _out1720, out _out1721);
              _3586_hExpr = _out1719;
              _3587___v116 = _out1720;
              _3588_recIdentsH = _out1721;
              _3578_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3578_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_3586_hExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3588_recIdentsH);
            }
          }
          r = _3574_onExpr;
          if (_3572_isArray) {
            if (!(_3577_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              _3577_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _3577_methodName);
            }
            r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _3577_methodName))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3578_arguments);
          } else {
            if (!(_3577_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              r = ((r).Sel(_3577_methodName)).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _3578_arguments);
            }
          }
          RAST._IExpr _out1722;
          DCOMP._IOwnership _out1723;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1722, out _out1723);
          r = _out1722;
          resultingOwnership = _out1723;
          return ;
        }
      } else if (_source145.is_TupleSelect) {
        DAST._IExpression _3589___mcc_h246 = _source145.dtor_expr;
        BigInteger _3590___mcc_h247 = _source145.dtor_index;
        BigInteger _3591_idx = _3590___mcc_h247;
        DAST._IExpression _3592_on = _3589___mcc_h246;
        {
          RAST._IExpr _3593_onExpr;
          DCOMP._IOwnership _3594_onOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3595_recIdents;
          RAST._IExpr _out1724;
          DCOMP._IOwnership _out1725;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1726;
          (this).GenExpr(_3592_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1724, out _out1725, out _out1726);
          _3593_onExpr = _out1724;
          _3594_onOwnership = _out1725;
          _3595_recIdents = _out1726;
          r = (_3593_onExpr).Sel(Std.Strings.__default.OfNat(_3591_idx));
          RAST._IExpr _out1727;
          DCOMP._IOwnership _out1728;
          DCOMP.COMP.FromOwnership(r, _3594_onOwnership, expectedOwnership, out _out1727, out _out1728);
          r = _out1727;
          resultingOwnership = _out1728;
          readIdents = _3595_recIdents;
          return ;
        }
      } else if (_source145.is_Call) {
        DAST._IExpression _3596___mcc_h248 = _source145.dtor_on;
        DAST._ICallName _3597___mcc_h249 = _source145.dtor_callName;
        Dafny.ISequence<DAST._IType> _3598___mcc_h250 = _source145.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _3599___mcc_h251 = _source145.dtor_args;
        Dafny.ISequence<DAST._IExpression> _3600_args = _3599___mcc_h251;
        Dafny.ISequence<DAST._IType> _3601_typeArgs = _3598___mcc_h250;
        DAST._ICallName _3602_name = _3597___mcc_h249;
        DAST._IExpression _3603_on = _3596___mcc_h248;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IType> _3604_typeExprs;
          _3604_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_3601_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _3605_typeI;
            _3605_typeI = BigInteger.Zero;
            while ((_3605_typeI) < (new BigInteger((_3601_typeArgs).Count))) {
              RAST._IType _3606_typeExpr;
              RAST._IType _out1729;
              _out1729 = (this).GenType((_3601_typeArgs).Select(_3605_typeI), false, false);
              _3606_typeExpr = _out1729;
              _3604_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_3604_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_3606_typeExpr));
              _3605_typeI = (_3605_typeI) + (BigInteger.One);
            }
          }
          Dafny.ISequence<RAST._IExpr> _3607_argExprs;
          _3607_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _3608_i;
          _3608_i = BigInteger.Zero;
          while ((_3608_i) < (new BigInteger((_3600_args).Count))) {
            RAST._IExpr _3609_argExpr;
            DCOMP._IOwnership _3610_argOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3611_argIdents;
            RAST._IExpr _out1730;
            DCOMP._IOwnership _out1731;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1732;
            (this).GenExpr((_3600_args).Select(_3608_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1730, out _out1731, out _out1732);
            _3609_argExpr = _out1730;
            _3610_argOwnership = _out1731;
            _3611_argIdents = _out1732;
            _3607_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_3607_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_3609_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3611_argIdents);
            _3608_i = (_3608_i) + (BigInteger.One);
          }
          RAST._IExpr _3612_onExpr;
          DCOMP._IOwnership _3613___v117;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3614_recIdents;
          RAST._IExpr _out1733;
          DCOMP._IOwnership _out1734;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1735;
          (this).GenExpr(_3603_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1733, out _out1734, out _out1735);
          _3612_onExpr = _out1733;
          _3613___v117 = _out1734;
          _3614_recIdents = _out1735;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3614_recIdents);
          Dafny.ISequence<Dafny.Rune> _3615_renderedName;
          _3615_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source151) => {
            if (_source151.is_Name) {
              Dafny.ISequence<Dafny.Rune> _3616___mcc_h276 = _source151.dtor_name;
              Dafny.ISequence<Dafny.Rune> _3617_ident = _3616___mcc_h276;
              return DCOMP.__default.escapeIdent(_3617_ident);
            } else if (_source151.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source151.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source151.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_3602_name);
          DAST._IExpression _source152 = _3603_on;
          if (_source152.is_Literal) {
            DAST._ILiteral _3618___mcc_h277 = _source152.dtor_Literal_a0;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _3619___mcc_h279 = _source152.dtor_Ident_a0;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3620___mcc_h281 = _source152.dtor_Companion_a0;
            {
              _3612_onExpr = (_3612_onExpr).MSel(_3615_renderedName);
            }
          } else if (_source152.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _3621___mcc_h283 = _source152.dtor_Tuple_a0;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3622___mcc_h285 = _source152.dtor_path;
            Dafny.ISequence<DAST._IType> _3623___mcc_h286 = _source152.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _3624___mcc_h287 = _source152.dtor_args;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _3625___mcc_h291 = _source152.dtor_dims;
            DAST._IType _3626___mcc_h292 = _source152.dtor_typ;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3627___mcc_h295 = _source152.dtor_path;
            Dafny.ISequence<DAST._IType> _3628___mcc_h296 = _source152.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _3629___mcc_h297 = _source152.dtor_variant;
            bool _3630___mcc_h298 = _source152.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3631___mcc_h299 = _source152.dtor_contents;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_Convert) {
            DAST._IExpression _3632___mcc_h305 = _source152.dtor_value;
            DAST._IType _3633___mcc_h306 = _source152.dtor_from;
            DAST._IType _3634___mcc_h307 = _source152.dtor_typ;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_SeqConstruct) {
            DAST._IExpression _3635___mcc_h311 = _source152.dtor_length;
            DAST._IExpression _3636___mcc_h312 = _source152.dtor_elem;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _3637___mcc_h315 = _source152.dtor_elements;
            DAST._IType _3638___mcc_h316 = _source152.dtor_typ;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _3639___mcc_h319 = _source152.dtor_elements;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _3640___mcc_h321 = _source152.dtor_elements;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3641___mcc_h323 = _source152.dtor_mapElems;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_MapBuilder) {
            DAST._IType _3642___mcc_h325 = _source152.dtor_keyType;
            DAST._IType _3643___mcc_h326 = _source152.dtor_valueType;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_SeqUpdate) {
            DAST._IExpression _3644___mcc_h329 = _source152.dtor_expr;
            DAST._IExpression _3645___mcc_h330 = _source152.dtor_indexExpr;
            DAST._IExpression _3646___mcc_h331 = _source152.dtor_value;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_MapUpdate) {
            DAST._IExpression _3647___mcc_h335 = _source152.dtor_expr;
            DAST._IExpression _3648___mcc_h336 = _source152.dtor_indexExpr;
            DAST._IExpression _3649___mcc_h337 = _source152.dtor_value;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_SetBuilder) {
            DAST._IType _3650___mcc_h341 = _source152.dtor_elemType;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_ToMultiset) {
            DAST._IExpression _3651___mcc_h343 = _source152.dtor_ToMultiset_a0;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_This) {
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_Ite) {
            DAST._IExpression _3652___mcc_h345 = _source152.dtor_cond;
            DAST._IExpression _3653___mcc_h346 = _source152.dtor_thn;
            DAST._IExpression _3654___mcc_h347 = _source152.dtor_els;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_UnOp) {
            DAST._IUnaryOp _3655___mcc_h351 = _source152.dtor_unOp;
            DAST._IExpression _3656___mcc_h352 = _source152.dtor_expr;
            DAST.Format._IUnaryOpFormat _3657___mcc_h353 = _source152.dtor_format1;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_BinOp) {
            DAST._IBinOp _3658___mcc_h357 = _source152.dtor_op;
            DAST._IExpression _3659___mcc_h358 = _source152.dtor_left;
            DAST._IExpression _3660___mcc_h359 = _source152.dtor_right;
            DAST.Format._IBinaryOpFormat _3661___mcc_h360 = _source152.dtor_format2;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_ArrayLen) {
            DAST._IExpression _3662___mcc_h365 = _source152.dtor_expr;
            BigInteger _3663___mcc_h366 = _source152.dtor_dim;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_MapKeys) {
            DAST._IExpression _3664___mcc_h369 = _source152.dtor_expr;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_MapValues) {
            DAST._IExpression _3665___mcc_h371 = _source152.dtor_expr;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_Select) {
            DAST._IExpression _3666___mcc_h373 = _source152.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _3667___mcc_h374 = _source152.dtor_field;
            bool _3668___mcc_h375 = _source152.dtor_isConstant;
            bool _3669___mcc_h376 = _source152.dtor_onDatatype;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_SelectFn) {
            DAST._IExpression _3670___mcc_h381 = _source152.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _3671___mcc_h382 = _source152.dtor_field;
            bool _3672___mcc_h383 = _source152.dtor_onDatatype;
            bool _3673___mcc_h384 = _source152.dtor_isStatic;
            BigInteger _3674___mcc_h385 = _source152.dtor_arity;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_Index) {
            DAST._IExpression _3675___mcc_h391 = _source152.dtor_expr;
            DAST._ICollKind _3676___mcc_h392 = _source152.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _3677___mcc_h393 = _source152.dtor_indices;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_IndexRange) {
            DAST._IExpression _3678___mcc_h397 = _source152.dtor_expr;
            bool _3679___mcc_h398 = _source152.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _3680___mcc_h399 = _source152.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _3681___mcc_h400 = _source152.dtor_high;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_TupleSelect) {
            DAST._IExpression _3682___mcc_h405 = _source152.dtor_expr;
            BigInteger _3683___mcc_h406 = _source152.dtor_index;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_Call) {
            DAST._IExpression _3684___mcc_h409 = _source152.dtor_on;
            DAST._ICallName _3685___mcc_h410 = _source152.dtor_callName;
            Dafny.ISequence<DAST._IType> _3686___mcc_h411 = _source152.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _3687___mcc_h412 = _source152.dtor_args;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _3688___mcc_h417 = _source152.dtor_params;
            DAST._IType _3689___mcc_h418 = _source152.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _3690___mcc_h419 = _source152.dtor_body;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _3691___mcc_h423 = _source152.dtor_values;
            DAST._IType _3692___mcc_h424 = _source152.dtor_retType;
            DAST._IExpression _3693___mcc_h425 = _source152.dtor_expr;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _3694___mcc_h429 = _source152.dtor_name;
            DAST._IType _3695___mcc_h430 = _source152.dtor_typ;
            DAST._IExpression _3696___mcc_h431 = _source152.dtor_value;
            DAST._IExpression _3697___mcc_h432 = _source152.dtor_iifeBody;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_Apply) {
            DAST._IExpression _3698___mcc_h437 = _source152.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _3699___mcc_h438 = _source152.dtor_args;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_TypeTest) {
            DAST._IExpression _3700___mcc_h441 = _source152.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3701___mcc_h442 = _source152.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _3702___mcc_h443 = _source152.dtor_variant;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_InitializationValue) {
            DAST._IType _3703___mcc_h447 = _source152.dtor_typ;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_BoolBoundedPool) {
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_SetBoundedPool) {
            DAST._IExpression _3704___mcc_h449 = _source152.dtor_of;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else if (_source152.is_SeqBoundedPool) {
            DAST._IExpression _3705___mcc_h451 = _source152.dtor_of;
            bool _3706___mcc_h452 = _source152.dtor_includeDuplicates;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          } else {
            DAST._IExpression _3707___mcc_h455 = _source152.dtor_lo;
            DAST._IExpression _3708___mcc_h456 = _source152.dtor_hi;
            {
              _3612_onExpr = (_3612_onExpr).Sel(_3615_renderedName);
            }
          }
          r = RAST.Expr.create_Call(_3612_onExpr, _3604_typeExprs, _3607_argExprs);
          RAST._IExpr _out1736;
          DCOMP._IOwnership _out1737;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1736, out _out1737);
          r = _out1736;
          resultingOwnership = _out1737;
          return ;
        }
      } else if (_source145.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _3709___mcc_h252 = _source145.dtor_params;
        DAST._IType _3710___mcc_h253 = _source145.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _3711___mcc_h254 = _source145.dtor_body;
        Dafny.ISequence<DAST._IStatement> _3712_body = _3711___mcc_h254;
        DAST._IType _3713_retType = _3710___mcc_h253;
        Dafny.ISequence<DAST._IFormal> _3714_params = _3709___mcc_h252;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3715_paramNames;
          _3715_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3716_i;
          _3716_i = BigInteger.Zero;
          while ((_3716_i) < (new BigInteger((_3714_params).Count))) {
            _3715_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_3715_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_3714_params).Select(_3716_i)).dtor_name));
            _3716_i = (_3716_i) + (BigInteger.One);
          }
          RAST._IExpr _3717_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3718_recIdents;
          RAST._IExpr _out1738;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1739;
          (this).GenStmts(_3712_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _3715_paramNames, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out1738, out _out1739);
          _3717_recursiveGen = _out1738;
          _3718_recIdents = _out1739;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _3719_allReadCloned;
          _3719_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_3718_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _3720_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_3718_recIdents).Elements) {
              _3720_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
              if ((_3718_recIdents).Contains(_3720_next)) {
                goto after__ASSIGN_SUCH_THAT_3;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 3286)");
          after__ASSIGN_SUCH_THAT_3: ;
            if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_3720_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
              if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                _3719_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(_3719_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let _this = self.clone();\n"));
              }
            } else if (!((_3715_paramNames).Contains(_3720_next))) {
              _3719_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3719_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent(_3720_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), DCOMP.__default.escapeIdent(_3720_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3720_next));
            }
            _3718_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_3718_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3720_next));
          }
          Dafny.ISequence<Dafny.Rune> _3721_paramsString;
          _3721_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          Dafny.ISequence<Dafny.Rune> _3722_paramTypes;
          _3722_paramTypes = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _3716_i = BigInteger.Zero;
          while ((_3716_i) < (new BigInteger((_3714_params).Count))) {
            if ((_3716_i).Sign == 1) {
              _3721_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_3721_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              _3722_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_3722_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IType _3723_typStr;
            RAST._IType _out1740;
            _out1740 = (this).GenType(((_3714_params).Select(_3716_i)).dtor_typ, false, true);
            _3723_typStr = _out1740;
            _3721_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3721_paramsString, DCOMP.__default.escapeIdent(((_3714_params).Select(_3716_i)).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (RAST.Type.create_Borrowed(_3723_typStr))._ToString(DCOMP.__default.IND));
            _3722_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_3722_paramTypes, (RAST.Type.create_Borrowed(_3723_typStr))._ToString(DCOMP.__default.IND));
            _3716_i = (_3716_i) + (BigInteger.One);
          }
          RAST._IType _3724_retTypeGen;
          RAST._IType _out1741;
          _out1741 = (this).GenType(_3713_retType, false, true);
          _3724_retTypeGen = _out1741;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn("), _3722_paramTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), (_3724_retTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>({\n")), _3719_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(move |")), _3721_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), (_3724_retTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), (_3717_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})")));
          RAST._IExpr _out1742;
          DCOMP._IOwnership _out1743;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1742, out _out1743);
          r = _out1742;
          resultingOwnership = _out1743;
          return ;
        }
      } else if (_source145.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _3725___mcc_h255 = _source145.dtor_values;
        DAST._IType _3726___mcc_h256 = _source145.dtor_retType;
        DAST._IExpression _3727___mcc_h257 = _source145.dtor_expr;
        DAST._IExpression _3728_expr = _3727___mcc_h257;
        DAST._IType _3729_retType = _3726___mcc_h256;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _3730_values = _3725___mcc_h255;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3731_paramNames;
          _3731_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3732_paramNamesSet;
          _3732_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3733_i;
          _3733_i = BigInteger.Zero;
          while ((_3733_i) < (new BigInteger((_3730_values).Count))) {
            _3731_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_3731_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((_3730_values).Select(_3733_i)).dtor__0).dtor_name));
            _3732_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3732_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((((_3730_values).Select(_3733_i)).dtor__0).dtor_name));
            _3733_i = (_3733_i) + (BigInteger.One);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _3734_s;
          _3734_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          Dafny.ISequence<Dafny.Rune> _3735_paramsString;
          _3735_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _3733_i = BigInteger.Zero;
          while ((_3733_i) < (new BigInteger((_3730_values).Count))) {
            if ((_3733_i).Sign == 1) {
              _3735_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_3735_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IType _3736_typStr;
            RAST._IType _out1744;
            _out1744 = (this).GenType((((_3730_values).Select(_3733_i)).dtor__0).dtor_typ, false, true);
            _3736_typStr = _out1744;
            RAST._IExpr _3737_valueGen;
            DCOMP._IOwnership _3738___v120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3739_recIdents;
            RAST._IExpr _out1745;
            DCOMP._IOwnership _out1746;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1747;
            (this).GenExpr(((_3730_values).Select(_3733_i)).dtor__1, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1745, out _out1746, out _out1747);
            _3737_valueGen = _out1745;
            _3738___v120 = _out1746;
            _3739_recIdents = _out1747;
            _3734_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3734_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent((((_3730_values).Select(_3733_i)).dtor__0).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_3736_typStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3739_recIdents);
            _3734_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3734_s, (_3737_valueGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            _3733_i = (_3733_i) + (BigInteger.One);
          }
          RAST._IExpr _3740_recGen;
          DCOMP._IOwnership _3741_recOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3742_recIdents;
          RAST._IExpr _out1748;
          DCOMP._IOwnership _out1749;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1750;
          (this).GenExpr(_3728_expr, selfIdent, _3731_paramNames, expectedOwnership, out _out1748, out _out1749, out _out1750);
          _3740_recGen = _out1748;
          _3741_recOwned = _out1749;
          _3742_recIdents = _out1750;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_3742_recIdents, _3732_paramNamesSet);
          _3734_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3734_s, (_3740_recGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          r = RAST.Expr.create_RawExpr(_3734_s);
          RAST._IExpr _out1751;
          DCOMP._IOwnership _out1752;
          DCOMP.COMP.FromOwnership(r, _3741_recOwned, expectedOwnership, out _out1751, out _out1752);
          r = _out1751;
          resultingOwnership = _out1752;
          return ;
        }
      } else if (_source145.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _3743___mcc_h258 = _source145.dtor_name;
        DAST._IType _3744___mcc_h259 = _source145.dtor_typ;
        DAST._IExpression _3745___mcc_h260 = _source145.dtor_value;
        DAST._IExpression _3746___mcc_h261 = _source145.dtor_iifeBody;
        DAST._IExpression _3747_iifeBody = _3746___mcc_h261;
        DAST._IExpression _3748_value = _3745___mcc_h260;
        DAST._IType _3749_tpe = _3744___mcc_h259;
        Dafny.ISequence<Dafny.Rune> _3750_name = _3743___mcc_h258;
        {
          RAST._IExpr _3751_valueGen;
          DCOMP._IOwnership _3752___v121;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3753_recIdents;
          RAST._IExpr _out1753;
          DCOMP._IOwnership _out1754;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1755;
          (this).GenExpr(_3748_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1753, out _out1754, out _out1755);
          _3751_valueGen = _out1753;
          _3752___v121 = _out1754;
          _3753_recIdents = _out1755;
          readIdents = _3753_recIdents;
          RAST._IType _3754_valueTypeGen;
          RAST._IType _out1756;
          _out1756 = (this).GenType(_3749_tpe, false, true);
          _3754_valueTypeGen = _out1756;
          RAST._IExpr _3755_bodyGen;
          DCOMP._IOwnership _3756___v122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3757_bodyIdents;
          RAST._IExpr _out1757;
          DCOMP._IOwnership _out1758;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1759;
          (this).GenExpr(_3747_iifeBody, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1757, out _out1758, out _out1759);
          _3755_bodyGen = _out1757;
          _3756___v122 = _out1758;
          _3757_bodyIdents = _out1759;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_3757_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_3750_name))));
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet "), DCOMP.__default.escapeIdent((_3750_name))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_3754_valueTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (_3751_valueGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), (_3755_bodyGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")));
          RAST._IExpr _out1760;
          DCOMP._IOwnership _out1761;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1760, out _out1761);
          r = _out1760;
          resultingOwnership = _out1761;
          return ;
        }
      } else if (_source145.is_Apply) {
        DAST._IExpression _3758___mcc_h262 = _source145.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _3759___mcc_h263 = _source145.dtor_args;
        Dafny.ISequence<DAST._IExpression> _3760_args = _3759___mcc_h263;
        DAST._IExpression _3761_func = _3758___mcc_h262;
        {
          RAST._IExpr _3762_funcExpr;
          DCOMP._IOwnership _3763___v123;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3764_recIdents;
          RAST._IExpr _out1762;
          DCOMP._IOwnership _out1763;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1764;
          (this).GenExpr(_3761_func, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1762, out _out1763, out _out1764);
          _3762_funcExpr = _out1762;
          _3763___v123 = _out1763;
          _3764_recIdents = _out1764;
          readIdents = _3764_recIdents;
          Dafny.ISequence<Dafny.Rune> _3765_argString;
          _3765_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _3766_i;
          _3766_i = BigInteger.Zero;
          while ((_3766_i) < (new BigInteger((_3760_args).Count))) {
            if ((_3766_i).Sign == 1) {
              _3765_argString = Dafny.Sequence<Dafny.Rune>.Concat(_3765_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            RAST._IExpr _3767_argExpr;
            DCOMP._IOwnership _3768_argOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3769_argIdents;
            RAST._IExpr _out1765;
            DCOMP._IOwnership _out1766;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1767;
            (this).GenExpr((_3760_args).Select(_3766_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1765, out _out1766, out _out1767);
            _3767_argExpr = _out1765;
            _3768_argOwned = _out1766;
            _3769_argIdents = _out1767;
            Dafny.ISequence<Dafny.Rune> _3770_argExprString;
            _3770_argExprString = (_3767_argExpr)._ToString(DCOMP.__default.IND);
            if (object.Equals(_3768_argOwned, DCOMP.Ownership.create_OwnershipOwned())) {
              _3770_argExprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _3770_argExprString);
            }
            _3765_argString = Dafny.Sequence<Dafny.Rune>.Concat(_3765_argString, _3770_argExprString);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3769_argIdents);
            _3766_i = (_3766_i) + (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_3762_funcExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _3765_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))")));
          RAST._IExpr _out1768;
          DCOMP._IOwnership _out1769;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1768, out _out1769);
          r = _out1768;
          resultingOwnership = _out1769;
          return ;
        }
      } else if (_source145.is_TypeTest) {
        DAST._IExpression _3771___mcc_h264 = _source145.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3772___mcc_h265 = _source145.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _3773___mcc_h266 = _source145.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _3774_variant = _3773___mcc_h266;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3775_dType = _3772___mcc_h265;
        DAST._IExpression _3776_on = _3771___mcc_h264;
        {
          RAST._IExpr _3777_exprGen;
          DCOMP._IOwnership _3778___v124;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3779_recIdents;
          RAST._IExpr _out1770;
          DCOMP._IOwnership _out1771;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1772;
          (this).GenExpr(_3776_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1770, out _out1771, out _out1772);
          _3777_exprGen = _out1770;
          _3778___v124 = _out1771;
          _3779_recIdents = _out1772;
          Dafny.ISequence<Dafny.Rune> _3780_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1773;
          _out1773 = DCOMP.COMP.GenPath(_3775_dType);
          _3780_dTypePath = _out1773;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), (_3777_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _3780_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_3774_variant)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })")));
          RAST._IExpr _out1774;
          DCOMP._IOwnership _out1775;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1774, out _out1775);
          r = _out1774;
          resultingOwnership = _out1775;
          readIdents = _3779_recIdents;
          return ;
        }
      } else if (_source145.is_InitializationValue) {
        DAST._IType _3781___mcc_h267 = _source145.dtor_typ;
        DAST._IType _3782_typ = _3781___mcc_h267;
        {
          RAST._IType _3783_typExpr;
          RAST._IType _out1776;
          _out1776 = (this).GenType(_3782_typ, false, false);
          _3783_typExpr = _out1776;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3783_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
          RAST._IExpr _out1777;
          DCOMP._IOwnership _out1778;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1777, out _out1778);
          r = _out1777;
          resultingOwnership = _out1778;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source145.is_BoolBoundedPool) {
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
      } else if (_source145.is_SetBoundedPool) {
        DAST._IExpression _3784___mcc_h268 = _source145.dtor_of;
        DAST._IExpression _3785_of = _3784___mcc_h268;
        {
          RAST._IExpr _3786_exprGen;
          DCOMP._IOwnership _3787___v125;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3788_recIdents;
          RAST._IExpr _out1781;
          DCOMP._IOwnership _out1782;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1783;
          (this).GenExpr(_3785_of, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1781, out _out1782, out _out1783);
          _3786_exprGen = _out1781;
          _3787___v125 = _out1782;
          _3788_recIdents = _out1783;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_3786_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").iter()")));
          RAST._IExpr _out1784;
          DCOMP._IOwnership _out1785;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1784, out _out1785);
          r = _out1784;
          resultingOwnership = _out1785;
          readIdents = _3788_recIdents;
          return ;
        }
      } else if (_source145.is_SeqBoundedPool) {
        DAST._IExpression _3789___mcc_h269 = _source145.dtor_of;
        bool _3790___mcc_h270 = _source145.dtor_includeDuplicates;
        bool _3791_includeDuplicates = _3790___mcc_h270;
        DAST._IExpression _3792_of = _3789___mcc_h269;
        {
          RAST._IExpr _3793_exprGen;
          DCOMP._IOwnership _3794___v126;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3795_recIdents;
          RAST._IExpr _out1786;
          DCOMP._IOwnership _out1787;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1788;
          (this).GenExpr(_3792_of, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1786, out _out1787, out _out1788);
          _3793_exprGen = _out1786;
          _3794___v126 = _out1787;
          _3795_recIdents = _out1788;
          Dafny.ISequence<Dafny.Rune> _3796_s;
          _3796_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_3793_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").iter()"));
          if (!(_3791_includeDuplicates)) {
            _3796_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::itertools::Itertools::unique("), _3796_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          r = RAST.Expr.create_RawExpr(_3796_s);
          RAST._IExpr _out1789;
          DCOMP._IOwnership _out1790;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1789, out _out1790);
          r = _out1789;
          resultingOwnership = _out1790;
          readIdents = _3795_recIdents;
          return ;
        }
      } else {
        DAST._IExpression _3797___mcc_h271 = _source145.dtor_lo;
        DAST._IExpression _3798___mcc_h272 = _source145.dtor_hi;
        DAST._IExpression _3799_hi = _3798___mcc_h272;
        DAST._IExpression _3800_lo = _3797___mcc_h271;
        {
          RAST._IExpr _3801_lo;
          DCOMP._IOwnership _3802___v127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3803_recIdentsLo;
          RAST._IExpr _out1791;
          DCOMP._IOwnership _out1792;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1793;
          (this).GenExpr(_3800_lo, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1791, out _out1792, out _out1793);
          _3801_lo = _out1791;
          _3802___v127 = _out1792;
          _3803_recIdentsLo = _out1793;
          RAST._IExpr _3804_hi;
          DCOMP._IOwnership _3805___v128;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3806_recIdentsHi;
          RAST._IExpr _out1794;
          DCOMP._IOwnership _out1795;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1796;
          (this).GenExpr(_3799_hi, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out1794, out _out1795, out _out1796);
          _3804_hi = _out1794;
          _3805___v128 = _out1795;
          _3806_recIdentsHi = _out1796;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::integer_range("), (_3801_lo)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), (_3804_hi)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          RAST._IExpr _out1797;
          DCOMP._IOwnership _out1798;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1797, out _out1798);
          r = _out1797;
          resultingOwnership = _out1798;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3803_recIdentsLo, _3806_recIdentsHi);
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
      BigInteger _3807_i;
      _3807_i = BigInteger.Zero;
      while ((_3807_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _3808_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _3809_m;
        RAST._IMod _out1799;
        _out1799 = (this).GenModule((p).Select(_3807_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _3809_m = _out1799;
        _3808_generated = (_3809_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_3807_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _3808_generated);
        _3807_i = (_3807_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _3810_i;
      _3810_i = BigInteger.Zero;
      while ((_3810_i) < (new BigInteger((fullName).Count))) {
        if ((_3810_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeIdent((fullName).Select(_3810_i)));
        _3810_i = (_3810_i) + (BigInteger.One);
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