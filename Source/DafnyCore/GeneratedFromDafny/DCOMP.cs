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
      Dafny.ISequence<Dafny.Rune> _984___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_984___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _984___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_984___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _984___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_984___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _985___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_985___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _985___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_985___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _985___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_985___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _986_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _986_r);
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
      this._i_UnicodeChars = false;
    }
    public void __ctor(bool UnicodeChars)
    {
      (this)._i_UnicodeChars = UnicodeChars;
    }
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<RAST._IModDecl> _987_body;
      Dafny.ISequence<RAST._IModDecl> _out15;
      _out15 = (this).GenModuleBody((mod).dtor_body, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
      _987_body = _out15;
      s = (((mod).dtor_isExtern) ? (RAST.Mod.create_ExternMod(DCOMP.__default.escapeIdent((mod).dtor_name))) : (RAST.Mod.create_Mod(DCOMP.__default.escapeIdent((mod).dtor_name), _987_body)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _988_i;
      _988_i = BigInteger.Zero;
      while ((_988_i) < (new BigInteger((body).Count))) {
        Dafny.ISequence<RAST._IModDecl> _989_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source41 = (body).Select(_988_i);
        bool unmatched41 = true;
        if (unmatched41) {
          if (_source41.is_Module) {
            DAST._IModule _990_m = _source41.dtor_Module_i_a0;
            unmatched41 = false;
            RAST._IMod _991_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_990_m, containingPath);
            _991_mm = _out16;
            _989_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_991_mm));
          }
        }
        if (unmatched41) {
          if (_source41.is_Class) {
            DAST._IClass _992_c = _source41.dtor_Class_i_a0;
            unmatched41 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_992_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_992_c).dtor_name)));
            _989_generated = _out17;
          }
        }
        if (unmatched41) {
          if (_source41.is_Trait) {
            DAST._ITrait _993_t = _source41.dtor_Trait_i_a0;
            unmatched41 = false;
            Dafny.ISequence<Dafny.Rune> _994_tt;
            Dafny.ISequence<Dafny.Rune> _out18;
            _out18 = (this).GenTrait(_993_t, containingPath);
            _994_tt = _out18;
            _989_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_994_tt));
          }
        }
        if (unmatched41) {
          if (_source41.is_Newtype) {
            DAST._INewtype _995_n = _source41.dtor_Newtype_i_a0;
            unmatched41 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_995_n);
            _989_generated = _out19;
          }
        }
        if (unmatched41) {
          DAST._IDatatype _996_d = _source41.dtor_Datatype_i_a0;
          unmatched41 = false;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenDatatype(_996_d);
          _989_generated = _out20;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _989_generated);
        _988_i = (_988_i) + (BigInteger.One);
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
      BigInteger _997_tpI;
      _997_tpI = BigInteger.Zero;
      if ((new BigInteger((@params).Count)).Sign == 1) {
        while ((_997_tpI) < (new BigInteger((@params).Count))) {
          DAST._IType _998_tp;
          _998_tp = (@params).Select(_997_tpI);
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_998_tp));
          RAST._IType _999_genTp;
          RAST._IType _out21;
          _out21 = (this).GenType(_998_tp, false, false);
          _999_genTp = _out21;
          typeParams = Dafny.Sequence<RAST._ITypeParam>.Concat(typeParams, Dafny.Sequence<RAST._ITypeParam>.FromElements(RAST.TypeParam.create((_999_genTp)._ToString(DCOMP.__default.IND), Dafny.Sequence<RAST._IType>.FromElements())));
          _997_tpI = (_997_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<RAST._IType> _1000_baseConstraints;
      _1000_baseConstraints = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.CloneTrait, RAST.__default.DafnyPrintTrait, RAST.__default.StaticTrait);
      constrainedTypeParams = RAST.TypeParam.AddConstraintsMultiple(typeParams, _1000_baseConstraints);
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1001_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1002_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1003_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1004_whereConstraints;
      Dafny.ISet<DAST._IType> _out22;
      Dafny.ISequence<RAST._ITypeParam> _out23;
      Dafny.ISequence<RAST._ITypeParam> _out24;
      Dafny.ISequence<Dafny.Rune> _out25;
      (this).GenTypeParameters((c).dtor_typeParams, out _out22, out _out23, out _out24, out _out25);
      _1001_typeParamsSet = _out22;
      _1002_sTypeParams = _out23;
      _1003_sConstrainedTypeParams = _out24;
      _1004_whereConstraints = _out25;
      Dafny.ISequence<Dafny.Rune> _1005_constrainedTypeParams;
      _1005_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1003_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IFormal> _1006_fields;
      _1006_fields = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1007_fieldInits;
      _1007_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _1008_fieldI;
      _1008_fieldI = BigInteger.Zero;
      while ((_1008_fieldI) < (new BigInteger(((c).dtor_fields).Count))) {
        DAST._IField _1009_field;
        _1009_field = ((c).dtor_fields).Select(_1008_fieldI);
        RAST._IType _1010_fieldType;
        RAST._IType _out26;
        _out26 = (this).GenType(((_1009_field).dtor_formal).dtor_typ, false, false);
        _1010_fieldType = _out26;
        _1006_fields = Dafny.Sequence<RAST._IFormal>.Concat(_1006_fields, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub "), DCOMP.__default.escapeIdent(((_1009_field).dtor_formal).dtor_name)), RAST.Type.create_TypeApp(RAST.__default.refcell__type, Dafny.Sequence<RAST._IType>.FromElements(_1010_fieldType)))));
        Std.Wrappers._IOption<DAST._IExpression> _source42 = (_1009_field).dtor_defaultValue;
        bool unmatched42 = true;
        if (unmatched42) {
          if (_source42.is_Some) {
            DAST._IExpression _1011_e = _source42.dtor_value;
            unmatched42 = false;
            {
              RAST._IExpr _1012_eStr;
              DCOMP._IOwnership _1013___v30;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1014___v31;
              RAST._IExpr _out27;
              DCOMP._IOwnership _out28;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out29;
              (this).GenExpr(_1011_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out27, out _out28, out _out29);
              _1012_eStr = _out27;
              _1013___v30 = _out28;
              _1014___v31 = _out29;
              _1007_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1007_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(((_1009_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_1012_eStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
            }
          }
        }
        if (unmatched42) {
          unmatched42 = false;
          {
            _1007_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1007_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(((_1009_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new(::std::default::Default::default())")))));
          }
        }
        _1008_fieldI = (_1008_fieldI) + (BigInteger.One);
      }
      BigInteger _1015_typeParamI;
      _1015_typeParamI = BigInteger.Zero;
      while ((_1015_typeParamI) < (new BigInteger(((c).dtor_typeParams).Count))) {
        RAST._IType _1016_tpeGen;
        RAST._IType _out30;
        _out30 = (this).GenType(((c).dtor_typeParams).Select(_1015_typeParamI), false, false);
        _1016_tpeGen = _out30;
        _1006_fields = Dafny.Sequence<RAST._IFormal>.Concat(_1006_fields, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1015_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1016_tpeGen)))));
        _1007_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1007_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1015_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
        _1015_typeParamI = (_1015_typeParamI) + (BigInteger.One);
      }
      RAST._IStruct _1017_struct;
      _1017_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.__default.escapeIdent((c).dtor_name), _1002_sTypeParams, RAST.Formals.create_NamedFormals(_1006_fields));
      Dafny.ISequence<RAST._IType> _1018_typeParamsAsTypes;
      _1018_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1019_typeParam) => {
        return RAST.__default.RawType((_1019_typeParam).dtor_content);
      })), _1002_sTypeParams);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1017_struct));
      Dafny.ISequence<RAST._IImplMember> _1020_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1021_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out31;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out32;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(path)), _1001_typeParamsSet, out _out31, out _out32);
      _1020_implBodyRaw = _out31;
      _1021_traitBodies = _out32;
      Dafny.ISequence<RAST._IImplMember> _1022_implBody;
      _1022_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(DCOMP.__default.escapeIdent((c).dtor_name), _1007_fieldInits))))), _1020_implBodyRaw);
      RAST._IImpl _1023_i;
      _1023_i = RAST.Impl.create_Impl(_1003_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1018_typeParamsAsTypes), _1004_whereConstraints, _1022_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1023_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _1024_i;
        _1024_i = BigInteger.Zero;
        while ((_1024_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _1025_superClass;
          _1025_superClass = ((c).dtor_superClasses).Select(_1024_i);
          DAST._IType _source43 = _1025_superClass;
          bool unmatched43 = true;
          if (unmatched43) {
            if (_source43.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1026_traitPath = _source43.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _1027_typeArgs = _source43.dtor_typeArgs;
              DAST._IResolvedType resolved0 = _source43.dtor_resolved;
              if (resolved0.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1028___v32 = resolved0.dtor_path;
                unmatched43 = false;
                {
                  Dafny.ISequence<Dafny.Rune> _1029_pathStr;
                  Dafny.ISequence<Dafny.Rune> _out33;
                  _out33 = DCOMP.COMP.GenPath(_1026_traitPath);
                  _1029_pathStr = _out33;
                  Dafny.ISequence<RAST._IType> _1030_typeArgs;
                  Dafny.ISequence<RAST._IType> _out34;
                  _out34 = (this).GenTypeArgs(_1027_typeArgs, false, false);
                  _1030_typeArgs = _out34;
                  Dafny.ISequence<RAST._IImplMember> _1031_body;
                  _1031_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((_1021_traitBodies).Contains(_1026_traitPath)) {
                    _1031_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1021_traitBodies,_1026_traitPath);
                  }
                  Dafny.ISequence<Dafny.Rune> _1032_genSelfPath;
                  Dafny.ISequence<Dafny.Rune> _out35;
                  _out35 = DCOMP.COMP.GenPath(path);
                  _1032_genSelfPath = _out35;
                  RAST._IModDecl _1033_x;
                  _1033_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1003_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1029_pathStr), _1030_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1032_genSelfPath), _1018_typeParamsAsTypes)), _1004_whereConstraints, _1031_body));
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1033_x));
                }
              }
            }
          }
          if (unmatched43) {
            DAST._IType _1034___v33 = _source43;
            unmatched43 = false;
          }
          _1024_i = (_1024_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _1035_d;
      _1035_d = RAST.Impl.create_ImplFor(_1003_sConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1018_typeParamsAsTypes), _1004_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _1036_defaultImpl;
      _1036_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1035_d));
      RAST._IImpl _1037_p;
      _1037_p = RAST.Impl.create_ImplFor(_1003_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1018_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), ((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _1038_printImpl;
      _1038_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1037_p));
      RAST._IImpl _1039_pp;
      _1039_pp = RAST.Impl.create_ImplFor(_1002_sTypeParams, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1018_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.Self)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _1040_ptrPartialEqImpl;
      _1040_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1039_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _1036_defaultImpl), _1038_printImpl), _1040_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _1041_typeParamsSet;
      _1041_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._IType> _1042_typeParams;
      _1042_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1043_tpI;
      _1043_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_1043_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._IType _1044_tp;
          _1044_tp = ((t).dtor_typeParams).Select(_1043_tpI);
          _1041_typeParamsSet = Dafny.Set<DAST._IType>.Union(_1041_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_1044_tp));
          RAST._IType _1045_genTp;
          RAST._IType _out36;
          _out36 = (this).GenType(_1044_tp, false, false);
          _1045_genTp = _out36;
          _1042_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1042_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1045_genTp));
          _1043_tpI = (_1043_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1046_fullPath;
      _1046_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1047_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1048___v34;
      Dafny.ISequence<RAST._IImplMember> _out37;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out38;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_1046_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_1046_fullPath)), _1041_typeParamsSet, out _out37, out _out38);
      _1047_implBody = _out37;
      _1048___v34 = _out38;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(Dafny.Sequence<RAST._ITypeParam>.FromElements(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((t).dtor_name)), _1042_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1047_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1049_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1050_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1051_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1052_whereConstraints;
      Dafny.ISet<DAST._IType> _out39;
      Dafny.ISequence<RAST._ITypeParam> _out40;
      Dafny.ISequence<RAST._ITypeParam> _out41;
      Dafny.ISequence<Dafny.Rune> _out42;
      (this).GenTypeParameters((c).dtor_typeParams, out _out39, out _out40, out _out41, out _out42);
      _1049_typeParamsSet = _out39;
      _1050_sTypeParams = _out40;
      _1051_sConstrainedTypeParams = _out41;
      _1052_whereConstraints = _out42;
      Dafny.ISequence<RAST._IType> _1053_typeParamsAsTypes;
      _1053_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1054_t) => {
        return RAST.__default.RawType((_1054_t).dtor_content);
      })), _1050_sTypeParams);
      Dafny.ISequence<Dafny.Rune> _1055_constrainedTypeParams;
      _1055_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1051_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1056_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source44 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched44 = true;
      if (unmatched44) {
        if (_source44.is_Some) {
          RAST._IType _1057_v = _source44.dtor_value;
          unmatched44 = false;
          _1056_underlyingType = _1057_v;
        }
      }
      if (unmatched44) {
        unmatched44 = false;
        RAST._IType _out43;
        _out43 = (this).GenType((c).dtor_base, false, false);
        _1056_underlyingType = _out43;
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), DCOMP.__default.escapeIdent((c).dtor_name), _1050_sTypeParams, RAST.Formals.create_NamelessFormals(Dafny.Sequence<RAST._INamelessFormal>.FromElements(RAST.NamelessFormal.create(RAST.Visibility.create_PUB(), _1056_underlyingType))))));
      Dafny.ISequence<Dafny.Rune> _1058_fnBody;
      _1058_fnBody = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Std.Wrappers._IOption<DAST._IExpression> _source45 = (c).dtor_witnessExpr;
      bool unmatched45 = true;
      if (unmatched45) {
        if (_source45.is_Some) {
          DAST._IExpression _1059_e = _source45.dtor_value;
          unmatched45 = false;
          {
            RAST._IExpr _1060_eStr;
            DCOMP._IOwnership _1061___v35;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1062___v36;
            RAST._IExpr _out44;
            DCOMP._IOwnership _out45;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out46;
            (this).GenExpr(_1059_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out44, out _out45, out _out46);
            _1060_eStr = _out44;
            _1061___v35 = _out45;
            _1062___v36 = _out46;
            _1058_fnBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1058_fnBody, DCOMP.__default.escapeIdent((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1060_eStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
          }
        }
      }
      if (unmatched45) {
        unmatched45 = false;
        {
          _1058_fnBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1058_fnBody, DCOMP.__default.escapeIdent((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(::std::default::Default::default())"));
        }
      }
      RAST._IImplMember _1063_body;
      _1063_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(_1058_fnBody))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1051_sConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1053_typeParamsAsTypes), _1052_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1063_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1051_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1053_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1051_sConstrainedTypeParams, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1053_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1056_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&Self::Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _1064_typeParamsSet;
      Dafny.ISequence<RAST._ITypeParam> _1065_sTypeParams;
      Dafny.ISequence<RAST._ITypeParam> _1066_sConstrainedTypeParams;
      Dafny.ISequence<Dafny.Rune> _1067_whereConstraints;
      Dafny.ISet<DAST._IType> _out47;
      Dafny.ISequence<RAST._ITypeParam> _out48;
      Dafny.ISequence<RAST._ITypeParam> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1064_typeParamsSet = _out47;
      _1065_sTypeParams = _out48;
      _1066_sConstrainedTypeParams = _out49;
      _1067_whereConstraints = _out50;
      Dafny.ISequence<RAST._IType> _1068_typeParamsAsTypes;
      _1068_typeParamsAsTypes = Std.Collections.Seq.__default.Map<RAST._ITypeParam, RAST._IType>(((System.Func<RAST._ITypeParam, RAST._IType>)((_1069_t) => {
        return RAST.__default.RawType((_1069_t).dtor_content);
      })), _1065_sTypeParams);
      Dafny.ISequence<Dafny.Rune> _1070_constrainedTypeParams;
      _1070_constrainedTypeParams = RAST.TypeParam.ToStringMultiple(_1066_sConstrainedTypeParams, Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.IND, DCOMP.__default.IND));
      Dafny.ISequence<RAST._IEnumCase> _1071_ctors;
      _1071_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _1072_i;
      _1072_i = BigInteger.Zero;
      while ((_1072_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1073_ctor;
        _1073_ctor = ((c).dtor_ctors).Select(_1072_i);
        Dafny.ISequence<RAST._IFormal> _1074_ctorArgs;
        _1074_ctorArgs = Dafny.Sequence<RAST._IFormal>.FromElements();
        BigInteger _1075_j;
        _1075_j = BigInteger.Zero;
        while ((_1075_j) < (new BigInteger(((_1073_ctor).dtor_args).Count))) {
          DAST._IFormal _1076_formal;
          _1076_formal = ((_1073_ctor).dtor_args).Select(_1075_j);
          RAST._IType _1077_formalType;
          RAST._IType _out51;
          _out51 = (this).GenType((_1076_formal).dtor_typ, false, false);
          _1077_formalType = _out51;
          if ((c).dtor_isCo) {
            _1074_ctorArgs = Dafny.Sequence<RAST._IFormal>.Concat(_1074_ctorArgs, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1076_formal).dtor_name), RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1077_formalType)))));
          } else {
            _1074_ctorArgs = Dafny.Sequence<RAST._IFormal>.Concat(_1074_ctorArgs, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1076_formal).dtor_name), _1077_formalType)));
          }
          _1075_j = (_1075_j) + (BigInteger.One);
        }
        _1071_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1071_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeIdent((_1073_ctor).dtor_name), RAST.Formals.create_NamedFormals(_1074_ctorArgs))));
        _1072_i = (_1072_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1078_selfPath;
      _1078_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1079_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1080_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out52;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out53;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(_1078_selfPath)), _1064_typeParamsSet, out _out52, out _out53);
      _1079_implBodyRaw = _out52;
      _1080_traitBodies = _out53;
      Dafny.ISequence<RAST._IImplMember> _1081_implBody;
      _1081_implBody = _1079_implBodyRaw;
      _1072_i = BigInteger.Zero;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1082_emittedFields;
      _1082_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      while ((_1072_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1083_ctor;
        _1083_ctor = ((c).dtor_ctors).Select(_1072_i);
        BigInteger _1084_j;
        _1084_j = BigInteger.Zero;
        while ((_1084_j) < (new BigInteger(((_1083_ctor).dtor_args).Count))) {
          DAST._IFormal _1085_formal;
          _1085_formal = ((_1083_ctor).dtor_args).Select(_1084_j);
          if (!((_1082_emittedFields).Contains((_1085_formal).dtor_name))) {
            _1082_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1082_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1085_formal).dtor_name));
            RAST._IType _1086_formalType;
            RAST._IType _out54;
            _out54 = (this).GenType((_1085_formal).dtor_typ, false, false);
            _1086_formalType = _out54;
            Dafny.ISequence<RAST._IMatchCase> _1087_cases;
            _1087_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _1088_k;
            _1088_k = BigInteger.Zero;
            while ((_1088_k) < (new BigInteger(((c).dtor_ctors).Count))) {
              DAST._IDatatypeCtor _1089_ctor2;
              _1089_ctor2 = ((c).dtor_ctors).Select(_1088_k);
              Dafny.ISequence<Dafny.Rune> _1090_pattern;
              _1090_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent((_1089_ctor2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              Dafny.ISequence<Dafny.Rune> _1091_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              BigInteger _1092_l;
              _1092_l = BigInteger.Zero;
              bool _1093_hasMatchingField;
              _1093_hasMatchingField = false;
              while ((_1092_l) < (new BigInteger(((_1089_ctor2).dtor_args).Count))) {
                DAST._IFormal _1094_formal2;
                _1094_formal2 = ((_1089_ctor2).dtor_args).Select(_1092_l);
                if (((_1085_formal).dtor_name).Equals((_1094_formal2).dtor_name)) {
                  _1093_hasMatchingField = true;
                }
                _1090_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1090_pattern, DCOMP.__default.escapeIdent((_1094_formal2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _1092_l = (_1092_l) + (BigInteger.One);
              }
              _1090_pattern = Dafny.Sequence<Dafny.Rune>.Concat(_1090_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              if (_1093_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _1091_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), DCOMP.__default.escapeIdent((_1085_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1091_rhs = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((_1085_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1091_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1095_ctorMatch;
              _1095_ctorMatch = RAST.MatchCase.create(_1090_pattern, RAST.Expr.create_RawExpr(_1091_rhs));
              _1087_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1087_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1095_ctorMatch));
              _1088_k = (_1088_k) + (BigInteger.One);
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1087_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1087_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1096_methodBody;
            _1096_methodBody = RAST.Expr.create_Match(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")), _1087_cases);
            _1081_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1081_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(DCOMP.__default.escapeIdent((_1085_formal).dtor_name), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1086_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1096_methodBody)))));
          }
          _1084_j = (_1084_j) + (BigInteger.One);
        }
        _1072_i = (_1072_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _1097_typeI;
        _1097_typeI = BigInteger.Zero;
        Dafny.ISequence<RAST._IType> _1098_types;
        _1098_types = Dafny.Sequence<RAST._IType>.FromElements();
        while ((_1097_typeI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          RAST._IType _1099_genTp;
          RAST._IType _out55;
          _out55 = (this).GenType(((c).dtor_typeParams).Select(_1097_typeI), false, false);
          _1099_genTp = _out55;
          _1098_types = Dafny.Sequence<RAST._IType>.Concat(_1098_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData::")), Dafny.Sequence<RAST._IType>.FromElements(_1099_genTp))));
          _1097_typeI = (_1097_typeI) + (BigInteger.One);
        }
        _1071_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1071_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Formals.create_NamelessFormals(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessFormal>(((System.Func<RAST._IType, RAST._INamelessFormal>)((_1100_tpe) => {
  return RAST.NamelessFormal.create(RAST.Visibility.create_PRIV(), _1100_tpe);
})), _1098_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1101_enumBody;
      _1101_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq)]")), DCOMP.__default.escapeIdent((c).dtor_name), _1065_sTypeParams, _1071_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1066_sConstrainedTypeParams, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1068_typeParamsAsTypes), _1067_whereConstraints, _1081_implBody)));
      _1072_i = BigInteger.Zero;
      Dafny.ISequence<RAST._IMatchCase> _1102_printImplBodyCases;
      _1102_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      while ((_1072_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _1103_ctor;
        _1103_ctor = ((c).dtor_ctors).Select(_1072_i);
        Dafny.ISequence<Dafny.Rune> _1104_ctorMatch;
        _1104_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((_1103_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _1105_modulePrefix;
        _1105_modulePrefix = (((((c).dtor_enclosingModule)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(((c).dtor_enclosingModule), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        RAST._IExpr _1106_printRhs;
        _1106_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1105_modulePrefix), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent((_1103_ctor).dtor_name)), (((_1103_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        BigInteger _1107_j;
        _1107_j = BigInteger.Zero;
        while ((_1107_j) < (new BigInteger(((_1103_ctor).dtor_args).Count))) {
          DAST._IFormal _1108_formal;
          _1108_formal = ((_1103_ctor).dtor_args).Select(_1107_j);
          _1104_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1104_ctorMatch, DCOMP.__default.escapeIdent((_1108_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1107_j).Sign == 1) {
            _1106_printRhs = (_1106_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1106_printRhs = (_1106_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), DCOMP.__default.escapeIdent((_1108_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
          _1107_j = (_1107_j) + (BigInteger.One);
        }
        _1104_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_1104_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_1103_ctor).dtor_hasAnyArgs) {
          _1106_printRhs = (_1106_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1106_printRhs = (_1106_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1102_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1102_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1104_ctorMatch), RAST.Expr.create_Block(_1106_printRhs))));
        _1072_i = (_1072_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1102_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1102_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      RAST._IExpr _1109_printImplBody;
      _1109_printImplBody = RAST.Expr.create_Match(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")), _1102_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1110_printImpl;
      _1110_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1066_sConstrainedTypeParams, RAST.__default.DafnyPrintTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1068_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool")))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1109_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1111_defaultImpl;
      _1111_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        _1072_i = BigInteger.Zero;
        Dafny.ISequence<Dafny.Rune> _1112_structName;
        _1112_structName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeIdent((c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1113_structAssignments;
        _1113_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        while ((_1072_i) < (new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count))) {
          DAST._IFormal _1114_formal;
          _1114_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1072_i);
          _1113_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1113_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent((_1114_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
          _1072_i = (_1072_i) + (BigInteger.One);
        }
        Dafny.ISequence<RAST._ITypeParam> _1115_defaultConstrainedTypeParams;
        _1115_defaultConstrainedTypeParams = RAST.TypeParam.AddConstraintsMultiple(_1065_sTypeParams, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        _1111_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1115_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeIdent((c).dtor_name)), _1068_typeParamsAsTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParam>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1112_structName, _1113_structAssignments))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1101_enumBody, _1110_printImpl), _1111_defaultImpl);
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
        BigInteger _1116_i;
        _1116_i = BigInteger.Zero;
        while ((_1116_i) < (new BigInteger((p).Count))) {
          if ((_1116_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeIdent(((p).Select(_1116_i))));
          _1116_i = (_1116_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _1117_i;
        _1117_i = BigInteger.Zero;
        while ((_1117_i) < (new BigInteger((args).Count))) {
          RAST._IType _1118_genTp;
          RAST._IType _out56;
          _out56 = (this).GenType((args).Select(_1117_i), inBinding, inFn);
          _1118_genTp = _out56;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1118_genTp));
          _1117_i = (_1117_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public RAST._IType GenType(DAST._IType c, bool inBinding, bool inFn)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source46 = c;
      bool unmatched46 = true;
      if (unmatched46) {
        if (_source46.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1119_p = _source46.dtor_Path_i_a0;
          Dafny.ISequence<DAST._IType> _1120_args = _source46.dtor_typeArgs;
          DAST._IResolvedType _1121_resolved = _source46.dtor_resolved;
          unmatched46 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1122_t;
            Dafny.ISequence<Dafny.Rune> _out57;
            _out57 = DCOMP.COMP.GenPath(_1119_p);
            _1122_t = _out57;
            s = RAST.Type.create_TIdentifier(_1122_t);
            Dafny.ISequence<RAST._IType> _1123_typeArgs;
            Dafny.ISequence<RAST._IType> _out58;
            _out58 = (this).GenTypeArgs(_1120_args, inBinding, inFn);
            _1123_typeArgs = _out58;
            s = RAST.Type.create_TypeApp(s, _1123_typeArgs);
            DAST._IResolvedType _source47 = _1121_resolved;
            bool unmatched47 = true;
            if (unmatched47) {
              if (_source47.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1124___v37 = _source47.dtor_path;
                unmatched47 = false;
                {
                  s = RAST.__default.Rc(s);
                }
              }
            }
            if (unmatched47) {
              if (_source47.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1125___v38 = _source47.dtor_path;
                unmatched47 = false;
                {
                  if ((_1119_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<dyn ::std::any::Any>"));
                  } else {
                    if (inBinding) {
                      s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
                    } else {
                      s = RAST.Type.create_ImplType(s);
                    }
                  }
                }
              }
            }
            if (unmatched47) {
              DAST._IType _1126_t = _source47.dtor_baseType;
              DAST._INewtypeRange _1127_range = _source47.dtor_range;
              bool _1128_erased = _source47.dtor_erase;
              unmatched47 = false;
              {
                if (_1128_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source48 = DCOMP.COMP.NewtypeToRustType(_1126_t, _1127_range);
                  bool unmatched48 = true;
                  if (unmatched48) {
                    if (_source48.is_Some) {
                      RAST._IType _1129_v = _source48.dtor_value;
                      unmatched48 = false;
                      s = _1129_v;
                    }
                  }
                  if (unmatched48) {
                    unmatched48 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_Nullable) {
          DAST._IType _1130_inner = _source46.dtor_Nullable_i_a0;
          unmatched46 = false;
          {
            RAST._IType _1131_innerExpr;
            RAST._IType _out59;
            _out59 = (this).GenType(_1130_inner, inBinding, inFn);
            _1131_innerExpr = _out59;
            s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_1131_innerExpr));
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1132_types = _source46.dtor_Tuple_i_a0;
          unmatched46 = false;
          {
            Dafny.ISequence<RAST._IType> _1133_args;
            _1133_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1134_i;
            _1134_i = BigInteger.Zero;
            while ((_1134_i) < (new BigInteger((_1132_types).Count))) {
              RAST._IType _1135_generated;
              RAST._IType _out60;
              _out60 = (this).GenType((_1132_types).Select(_1134_i), inBinding, inFn);
              _1135_generated = _out60;
              _1133_args = Dafny.Sequence<RAST._IType>.Concat(_1133_args, Dafny.Sequence<RAST._IType>.FromElements(_1135_generated));
              _1134_i = (_1134_i) + (BigInteger.One);
            }
            s = RAST.Type.create_TupleType(_1133_args);
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_Array) {
          DAST._IType _1136_element = _source46.dtor_element;
          BigInteger _1137_dims = _source46.dtor_dims;
          unmatched46 = false;
          {
            RAST._IType _1138_elem;
            RAST._IType _out61;
            _out61 = (this).GenType(_1136_element, inBinding, inFn);
            _1138_elem = _out61;
            s = _1138_elem;
            BigInteger _1139_i;
            _1139_i = BigInteger.Zero;
            while ((_1139_i) < (_1137_dims)) {
              s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
              _1139_i = (_1139_i) + (BigInteger.One);
            }
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_Seq) {
          DAST._IType _1140_element = _source46.dtor_element;
          unmatched46 = false;
          {
            RAST._IType _1141_elem;
            RAST._IType _out62;
            _out62 = (this).GenType(_1140_element, inBinding, inFn);
            _1141_elem = _out62;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1141_elem));
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_Set) {
          DAST._IType _1142_element = _source46.dtor_element;
          unmatched46 = false;
          {
            RAST._IType _1143_elem;
            RAST._IType _out63;
            _out63 = (this).GenType(_1142_element, inBinding, inFn);
            _1143_elem = _out63;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1143_elem));
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_Multiset) {
          DAST._IType _1144_element = _source46.dtor_element;
          unmatched46 = false;
          {
            RAST._IType _1145_elem;
            RAST._IType _out64;
            _out64 = (this).GenType(_1144_element, inBinding, inFn);
            _1145_elem = _out64;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1145_elem));
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_Map) {
          DAST._IType _1146_key = _source46.dtor_key;
          DAST._IType _1147_value = _source46.dtor_value;
          unmatched46 = false;
          {
            RAST._IType _1148_keyType;
            RAST._IType _out65;
            _out65 = (this).GenType(_1146_key, inBinding, inFn);
            _1148_keyType = _out65;
            RAST._IType _1149_valueType;
            RAST._IType _out66;
            _out66 = (this).GenType(_1147_value, inBinding, inFn);
            _1149_valueType = _out66;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1148_keyType, _1149_valueType));
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_MapBuilder) {
          DAST._IType _1150_key = _source46.dtor_key;
          DAST._IType _1151_value = _source46.dtor_value;
          unmatched46 = false;
          {
            RAST._IType _1152_keyType;
            RAST._IType _out67;
            _out67 = (this).GenType(_1150_key, inBinding, inFn);
            _1152_keyType = _out67;
            RAST._IType _1153_valueType;
            RAST._IType _out68;
            _out68 = (this).GenType(_1151_value, inBinding, inFn);
            _1153_valueType = _out68;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1152_keyType, _1153_valueType));
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_SetBuilder) {
          DAST._IType _1154_elem = _source46.dtor_element;
          unmatched46 = false;
          {
            RAST._IType _1155_elemType;
            RAST._IType _out69;
            _out69 = (this).GenType(_1154_elem, inBinding, inFn);
            _1155_elemType = _out69;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1155_elemType));
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1156_args = _source46.dtor_args;
          DAST._IType _1157_result = _source46.dtor_result;
          unmatched46 = false;
          {
            Dafny.ISequence<RAST._IType> _1158_argTypes;
            _1158_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1159_i;
            _1159_i = BigInteger.Zero;
            while ((_1159_i) < (new BigInteger((_1156_args).Count))) {
              RAST._IType _1160_generated;
              RAST._IType _out70;
              _out70 = (this).GenType((_1156_args).Select(_1159_i), inBinding, true);
              _1160_generated = _out70;
              _1158_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1158_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1160_generated)));
              _1159_i = (_1159_i) + (BigInteger.One);
            }
            RAST._IType _1161_resultType;
            RAST._IType _out71;
            _out71 = (this).GenType(_1157_result, inBinding, (inFn) || (inBinding));
            _1161_resultType = _out71;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("FunctionWrapper")), Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_FnType(_1158_argTypes, RAST.Type.create_IntersectionType(_1161_resultType, RAST.__default.StaticTrait))));
          }
        }
      }
      if (unmatched46) {
        if (_source46.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h100 = _source46.dtor_TypeArg_i_a0;
          Dafny.ISequence<Dafny.Rune> _1162_name = _h100;
          unmatched46 = false;
          s = RAST.__default.RawType(DCOMP.__default.escapeIdent(_1162_name));
        }
      }
      if (unmatched46) {
        if (_source46.is_Primitive) {
          DAST._IPrimitive _1163_p = _source46.dtor_Primitive_i_a0;
          unmatched46 = false;
          {
            DAST._IPrimitive _source49 = _1163_p;
            bool unmatched49 = true;
            if (unmatched49) {
              if (_source49.is_Int) {
                unmatched49 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched49) {
              if (_source49.is_Real) {
                unmatched49 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched49) {
              if (_source49.is_String) {
                unmatched49 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched49) {
              if (_source49.is_Bool) {
                unmatched49 = false;
                s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool"));
              }
            }
            if (unmatched49) {
              unmatched49 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched46) {
        Dafny.ISequence<Dafny.Rune> _1164_v = _source46.dtor_Passthrough_i_a0;
        unmatched46 = false;
        s = RAST.__default.RawType(_1164_v);
      }
      return s;
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _1165_i;
      _1165_i = BigInteger.Zero;
      while ((_1165_i) < (new BigInteger((body).Count))) {
        DAST._IMethod _source50 = (body).Select(_1165_i);
        bool unmatched50 = true;
        if (unmatched50) {
          DAST._IMethod _1166_m = _source50;
          unmatched50 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source51 = (_1166_m).dtor_overridingPath;
            bool unmatched51 = true;
            if (unmatched51) {
              if (_source51.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1167_p = _source51.dtor_value;
                unmatched51 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1168_existing;
                  _1168_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1167_p)) {
                    _1168_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1167_p);
                  }
                  RAST._IImplMember _1169_genMethod;
                  RAST._IImplMember _out72;
                  _out72 = (this).GenMethod(_1166_m, true, enclosingType, enclosingTypeParams);
                  _1169_genMethod = _out72;
                  _1168_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1168_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1169_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1167_p, _1168_existing)));
                }
              }
            }
            if (unmatched51) {
              unmatched51 = false;
              {
                RAST._IImplMember _1170_generated;
                RAST._IImplMember _out73;
                _out73 = (this).GenMethod(_1166_m, forTrait, enclosingType, enclosingTypeParams);
                _1170_generated = _out73;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1170_generated));
              }
            }
          }
        }
        _1165_i = (_1165_i) + (BigInteger.One);
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _1171_i;
      _1171_i = BigInteger.Zero;
      while ((_1171_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _1172_param;
        _1172_param = (@params).Select(_1171_i);
        RAST._IType _1173_paramType;
        RAST._IType _out74;
        _out74 = (this).GenType((_1172_param).dtor_typ, false, false);
        _1173_paramType = _out74;
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeIdent((_1172_param).dtor_name), RAST.Type.create_Borrowed(_1173_paramType))));
        _1171_i = (_1171_i) + (BigInteger.One);
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1174_params;
      Dafny.ISequence<RAST._IFormal> _out75;
      _out75 = (this).GenParams((m).dtor_params);
      _1174_params = _out75;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1175_paramNames;
      _1175_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1176_paramI;
      _1176_paramI = BigInteger.Zero;
      while ((_1176_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _1175_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1175_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_1176_paramI)).dtor_name));
        _1176_paramI = (_1176_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _1174_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.self), _1174_params);
        } else {
          RAST._IType _1177_tpe;
          RAST._IType _out76;
          _out76 = (this).GenType(enclosingType, false, false);
          _1177_tpe = _out76;
          _1174_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.Type.create_Borrowed(_1177_tpe))), _1174_params);
        }
      }
      Dafny.ISequence<RAST._IType> _1178_retTypeArgs;
      _1178_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1179_typeI;
      _1179_typeI = BigInteger.Zero;
      while ((_1179_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1180_typeExpr;
        RAST._IType _out77;
        _out77 = (this).GenType(((m).dtor_outTypes).Select(_1179_typeI), false, false);
        _1180_typeExpr = _out77;
        _1178_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1178_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1180_typeExpr));
        _1179_typeI = (_1179_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1181_visibility;
      _1181_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<Dafny.Rune> _1182_fnName;
      _1182_fnName = DCOMP.__default.escapeIdent((m).dtor_name);
      Dafny.ISequence<DAST._IType> _1183_typeParamsFiltered;
      _1183_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _1184_typeParamI;
      _1184_typeParamI = BigInteger.Zero;
      while ((_1184_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _1185_typeParam;
        _1185_typeParam = ((m).dtor_typeParams).Select(_1184_typeParamI);
        if (!((enclosingTypeParams).Contains(_1185_typeParam))) {
          _1183_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_1183_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_1185_typeParam));
        }
        _1184_typeParamI = (_1184_typeParamI) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.Rune> _1186_whereClauses;
      _1186_whereClauses = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Dafny.ISequence<RAST._ITypeParam> _1187_typeParams;
      _1187_typeParams = Dafny.Sequence<RAST._ITypeParam>.FromElements();
      if ((new BigInteger((_1183_typeParamsFiltered).Count)).Sign == 1) {
        _1186_whereClauses = Dafny.Sequence<Dafny.Rune>.Concat(_1186_whereClauses, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" where "));
        BigInteger _1188_i;
        _1188_i = BigInteger.Zero;
        while ((_1188_i) < (new BigInteger((_1183_typeParamsFiltered).Count))) {
          RAST._IType _1189_typeExpr;
          RAST._IType _out78;
          _out78 = (this).GenType((_1183_typeParamsFiltered).Select(_1188_i), false, false);
          _1189_typeExpr = _out78;
          _1187_typeParams = Dafny.Sequence<RAST._ITypeParam>.Concat(_1187_typeParams, Dafny.Sequence<RAST._ITypeParam>.FromElements(RAST.TypeParam.create((_1189_typeExpr)._ToString(DCOMP.__default.IND), Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.CloneTrait, RAST.__default.DafnyPrintTrait, RAST.__default.DefaultTrait, RAST.__default.StaticTrait))));
          _1188_i = (_1188_i) + (BigInteger.One);
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1190_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1191_earlyReturn;
        _1191_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source52 = (m).dtor_outVars;
        bool unmatched52 = true;
        if (unmatched52) {
          if (_source52.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1192_outVars = _source52.dtor_value;
            unmatched52 = false;
            {
              Dafny.ISequence<RAST._IExpr> _1193_tupleArgs;
              _1193_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _1194_outI;
              _1194_outI = BigInteger.Zero;
              while ((_1194_outI) < (new BigInteger((_1192_outVars).Count))) {
                Dafny.ISequence<Dafny.Rune> _1195_outVar;
                _1195_outVar = (_1192_outVars).Select(_1194_outI);
                _1193_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1193_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent((_1195_outVar)))));
                _1194_outI = (_1194_outI) + (BigInteger.One);
              }
              _1191_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1193_tupleArgs)));
            }
          }
        }
        if (unmatched52) {
          unmatched52 = false;
        }
        RAST._IExpr _1196_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1197___v39;
        RAST._IExpr _out79;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out80;
        (this).GenStmts((m).dtor_body, (((m).dtor_isStatic) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))), _1175_paramNames, true, _1191_earlyReturn, out _out79, out _out80);
        _1196_body = _out79;
        _1197___v39 = _out80;
        _1190_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some(_1196_body);
      } else {
        _1190_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1181_visibility, RAST.Fn.create(_1182_fnName, _1187_typeParams, _1174_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1178_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1178_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1178_retTypeArgs)))), _1186_whereClauses, _1190_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1198_declarations;
      _1198_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1199_i;
      _1199_i = BigInteger.Zero;
      while ((_1199_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _1200_stmt;
        _1200_stmt = (stmts).Select(_1199_i);
        RAST._IExpr _1201_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1202_recIdents;
        RAST._IExpr _out81;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out82;
        (this).GenStmt(_1200_stmt, selfIdent, @params, (isLast) && ((_1199_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out81, out _out82);
        _1201_stmtExpr = _out81;
        _1202_recIdents = _out82;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1202_recIdents, _1198_declarations));
        DAST._IStatement _source53 = _1200_stmt;
        bool unmatched53 = true;
        if (unmatched53) {
          if (_source53.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1203_name = _source53.dtor_name;
            DAST._IType _1204___v40 = _source53.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1205___v41 = _source53.dtor_maybeValue;
            unmatched53 = false;
            {
              _1198_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1198_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1203_name));
            }
          }
        }
        if (unmatched53) {
          DAST._IStatement _1206___v42 = _source53;
          unmatched53 = false;
        }
        generated = (generated).Then(_1201_stmtExpr);
        _1199_i = (_1199_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, Dafny.ISequence<Dafny.Rune> rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, out Dafny.ISequence<Dafny.Rune> generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IAssignLhs _source54 = lhs;
      bool unmatched54 = true;
      if (unmatched54) {
        if (_source54.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _h130 = _source54.dtor_Ident_i_a0;
          Dafny.ISequence<Dafny.Rune> _1207_id = _h130;
          unmatched54 = false;
          {
            if ((@params).Contains(_1207_id)) {
              generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), DCOMP.__default.escapeIdent(_1207_id));
            } else {
              generated = DCOMP.__default.escapeIdent(_1207_id);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1207_id);
            needsIIFE = false;
          }
        }
      }
      if (unmatched54) {
        if (_source54.is_Select) {
          DAST._IExpression _1208_on = _source54.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1209_field = _source54.dtor_field;
          unmatched54 = false;
          {
            RAST._IExpr _1210_onExpr;
            DCOMP._IOwnership _1211_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1212_recIdents;
            RAST._IExpr _out83;
            DCOMP._IOwnership _out84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out85;
            (this).GenExpr(_1208_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out83, out _out84, out _out85);
            _1210_onExpr = _out83;
            _1211_onOwned = _out84;
            _1212_recIdents = _out85;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_1210_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_1209_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = _1212_recIdents;
            needsIIFE = true;
          }
        }
      }
      if (unmatched54) {
        DAST._IExpression _1213_on = _source54.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1214_indices = _source54.dtor_indices;
        unmatched54 = false;
        {
          RAST._IExpr _1215_onExpr;
          DCOMP._IOwnership _1216_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1217_recIdents;
          RAST._IExpr _out86;
          DCOMP._IOwnership _out87;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out88;
          (this).GenExpr(_1213_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out86, out _out87, out _out88);
          _1215_onExpr = _out86;
          _1216_onOwned = _out87;
          _1217_recIdents = _out88;
          readIdents = _1217_recIdents;
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _1218_i;
          _1218_i = BigInteger.Zero;
          while ((_1218_i) < (new BigInteger((_1214_indices).Count))) {
            RAST._IExpr _1219_idx;
            DCOMP._IOwnership _1220___v43;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1221_recIdentsIdx;
            RAST._IExpr _out89;
            DCOMP._IOwnership _out90;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
            (this).GenExpr((_1214_indices).Select(_1218_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out89, out _out90, out _out91);
            _1219_idx = _out89;
            _1220___v43 = _out90;
            _1221_recIdentsIdx = _out91;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_1218_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_1219_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1221_recIdentsIdx);
            _1218_i = (_1218_i) + (BigInteger.One);
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, (_1215_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _1218_i = BigInteger.Zero;
          while ((_1218_i) < (new BigInteger((_1214_indices).Count))) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_1218_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _1218_i = (_1218_i) + (BigInteger.One);
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
      DAST._IStatement _source55 = stmt;
      bool unmatched55 = true;
      if (unmatched55) {
        if (_source55.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1222_name = _source55.dtor_name;
          DAST._IType _1223_typ = _source55.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source55.dtor_maybeValue;
          if (maybeValue0.is_Some) {
            DAST._IExpression _1224_expression = maybeValue0.dtor_value;
            unmatched55 = false;
            {
              RAST._IType _1225_typeString;
              RAST._IType _out92;
              _out92 = (this).GenType(_1223_typ, true, false);
              _1225_typeString = _out92;
              RAST._IExpr _1226_expr;
              DCOMP._IOwnership _1227___v44;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1228_recIdents;
              RAST._IExpr _out93;
              DCOMP._IOwnership _out94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out95;
              (this).GenExpr(_1224_expression, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out93, out _out94, out _out95);
              _1226_expr = _out93;
              _1227___v44 = _out94;
              _1228_recIdents = _out95;
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_1222_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1225_typeString), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1226_expr));
              readIdents = _1228_recIdents;
            }
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1229_name = _source55.dtor_name;
          DAST._IType _1230_typ = _source55.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source55.dtor_maybeValue;
          if (maybeValue1.is_None) {
            unmatched55 = false;
            {
              RAST._IType _1231_typeString;
              RAST._IType _out96;
              _out96 = (this).GenType(_1230_typ, true, false);
              _1231_typeString = _out96;
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_1229_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1231_typeString), Std.Wrappers.Option<RAST._IExpr>.create_None());
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_Assign) {
          DAST._IAssignLhs _1232_lhs = _source55.dtor_lhs;
          DAST._IExpression _1233_expression = _source55.dtor_value;
          unmatched55 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1234_lhsGen;
            bool _1235_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1236_recIdents;
            Dafny.ISequence<Dafny.Rune> _out97;
            bool _out98;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out99;
            (this).GenAssignLhs(_1232_lhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), selfIdent, @params, out _out97, out _out98, out _out99);
            _1234_lhsGen = _out97;
            _1235_needsIIFE = _out98;
            _1236_recIdents = _out99;
            RAST._IExpr _1237_exprGen;
            DCOMP._IOwnership _1238___v45;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1239_exprIdents;
            RAST._IExpr _out100;
            DCOMP._IOwnership _out101;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
            (this).GenExpr(_1233_expression, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out100, out _out101, out _out102);
            _1237_exprGen = _out100;
            _1238___v45 = _out101;
            _1239_exprIdents = _out102;
            if (_1235_needsIIFE) {
              generated = RAST.Expr.create_Block(RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1237_exprGen)), RAST.Expr.create_RawExpr(_1234_lhsGen)));
            } else {
              generated = RAST.Expr.create_AssignVar(_1234_lhsGen, _1237_exprGen);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1236_recIdents, _1239_exprIdents);
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_If) {
          DAST._IExpression _1240_cond = _source55.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1241_thn = _source55.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1242_els = _source55.dtor_els;
          unmatched55 = false;
          {
            RAST._IExpr _1243_cond;
            DCOMP._IOwnership _1244___v46;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1245_recIdents;
            RAST._IExpr _out103;
            DCOMP._IOwnership _out104;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
            (this).GenExpr(_1240_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out103, out _out104, out _out105);
            _1243_cond = _out103;
            _1244___v46 = _out104;
            _1245_recIdents = _out105;
            Dafny.ISequence<Dafny.Rune> _1246_condString;
            _1246_condString = (_1243_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1245_recIdents;
            RAST._IExpr _1247_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1248_thnIdents;
            RAST._IExpr _out106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
            (this).GenStmts(_1241_thn, selfIdent, @params, isLast, earlyReturn, out _out106, out _out107);
            _1247_thn = _out106;
            _1248_thnIdents = _out107;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1248_thnIdents);
            RAST._IExpr _1249_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1250_elsIdents;
            RAST._IExpr _out108;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out109;
            (this).GenStmts(_1242_els, selfIdent, @params, isLast, earlyReturn, out _out108, out _out109);
            _1249_els = _out108;
            _1250_elsIdents = _out109;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1250_elsIdents);
            generated = RAST.Expr.create_IfExpr(_1243_cond, _1247_thn, _1249_els);
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1251_lbl = _source55.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1252_body = _source55.dtor_body;
          unmatched55 = false;
          {
            RAST._IExpr _1253_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1254_bodyIdents;
            RAST._IExpr _out110;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
            (this).GenStmts(_1252_body, selfIdent, @params, isLast, earlyReturn, out _out110, out _out111);
            _1253_body = _out110;
            _1254_bodyIdents = _out111;
            readIdents = _1254_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1251_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1253_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_While) {
          DAST._IExpression _1255_cond = _source55.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1256_body = _source55.dtor_body;
          unmatched55 = false;
          {
            RAST._IExpr _1257_cond;
            DCOMP._IOwnership _1258___v47;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1259_recIdents;
            RAST._IExpr _out112;
            DCOMP._IOwnership _out113;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
            (this).GenExpr(_1255_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out112, out _out113, out _out114);
            _1257_cond = _out112;
            _1258___v47 = _out113;
            _1259_recIdents = _out114;
            readIdents = _1259_recIdents;
            RAST._IExpr _1260_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1261_bodyIdents;
            RAST._IExpr _out115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
            (this).GenStmts(_1256_body, selfIdent, @params, false, earlyReturn, out _out115, out _out116);
            _1260_body = _out115;
            _1261_bodyIdents = _out116;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1261_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1257_cond), _1260_body);
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1262_boundName = _source55.dtor_boundName;
          DAST._IType _1263_boundType = _source55.dtor_boundType;
          DAST._IExpression _1264_over = _source55.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1265_body = _source55.dtor_body;
          unmatched55 = false;
          {
            RAST._IExpr _1266_over;
            DCOMP._IOwnership _1267___v48;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1268_recIdents;
            RAST._IExpr _out117;
            DCOMP._IOwnership _out118;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
            (this).GenExpr(_1264_over, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out117, out _out118, out _out119);
            _1266_over = _out117;
            _1267___v48 = _out118;
            _1268_recIdents = _out119;
            RAST._IType _1269_boundTypeStr;
            RAST._IType _out120;
            _out120 = (this).GenType(_1263_boundType, false, false);
            _1269_boundTypeStr = _out120;
            readIdents = _1268_recIdents;
            RAST._IExpr _1270_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1271_bodyIdents;
            RAST._IExpr _out121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
            (this).GenStmts(_1265_body, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1262_boundName)), false, earlyReturn, out _out121, out _out122);
            _1270_body = _out121;
            _1271_bodyIdents = _out122;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1271_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1262_boundName));
            generated = RAST.Expr.create_For(DCOMP.__default.escapeIdent(_1262_boundName), _1266_over, _1270_body);
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1272_toLabel = _source55.dtor_toLabel;
          unmatched55 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source56 = _1272_toLabel;
            bool unmatched56 = true;
            if (unmatched56) {
              if (_source56.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1273_lbl = _source56.dtor_value;
                unmatched56 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1273_lbl)));
                }
              }
            }
            if (unmatched56) {
              unmatched56 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1274_body = _source55.dtor_body;
          unmatched55 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self.clone()")))));
            }
            BigInteger _1275_paramI;
            _1275_paramI = BigInteger.Zero;
            while ((_1275_paramI) < (new BigInteger((@params).Count))) {
              Dafny.ISequence<Dafny.Rune> _1276_param;
              _1276_param = (@params).Select(_1275_paramI);
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeIdent(_1276_param), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.Clone(RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent(_1276_param))))));
              _1275_paramI = (_1275_paramI) + (BigInteger.One);
            }
            RAST._IExpr _1277_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1278_bodyIdents;
            RAST._IExpr _out123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
            (this).GenStmts(_1274_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out123, out _out124);
            _1277_body = _out123;
            _1278_bodyIdents = _out124;
            readIdents = _1278_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1277_body)));
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_JumpTailCallStart) {
          unmatched55 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_Call) {
          DAST._IExpression _1279_on = _source55.dtor_on;
          DAST._ICallName _1280_name = _source55.dtor_callName;
          Dafny.ISequence<DAST._IType> _1281_typeArgs = _source55.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1282_args = _source55.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1283_maybeOutVars = _source55.dtor_outs;
          unmatched55 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<Dafny.Rune> _1284_typeArgString;
            _1284_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            if ((new BigInteger((_1281_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _1285_typeI;
              _1285_typeI = BigInteger.Zero;
              Dafny.ISequence<RAST._IType> _1286_typeArgsR;
              _1286_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
              while ((_1285_typeI) < (new BigInteger((_1281_typeArgs).Count))) {
                RAST._IType _1287_tpe;
                RAST._IType _out125;
                _out125 = (this).GenType((_1281_typeArgs).Select(_1285_typeI), false, false);
                _1287_tpe = _out125;
                _1286_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_1286_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_1287_tpe));
                _1285_typeI = (_1285_typeI) + (BigInteger.One);
              }
              _1284_typeArgString = (RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1286_typeArgsR))._ToString(DCOMP.__default.IND);
            }
            Dafny.ISequence<Dafny.Rune> _1288_argString;
            _1288_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _1289_i;
            _1289_i = BigInteger.Zero;
            while ((_1289_i) < (new BigInteger((_1282_args).Count))) {
              if ((_1289_i).Sign == 1) {
                _1288_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1288_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              RAST._IExpr _1290_argExpr;
              DCOMP._IOwnership _1291_ownership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1292_argIdents;
              RAST._IExpr _out126;
              DCOMP._IOwnership _out127;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
              (this).GenExpr((_1282_args).Select(_1289_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out126, out _out127, out _out128);
              _1290_argExpr = _out126;
              _1291_ownership = _out127;
              _1292_argIdents = _out128;
              Dafny.ISequence<Dafny.Rune> _1293_argExprString;
              _1293_argExprString = (_1290_argExpr)._ToString(DCOMP.__default.IND);
              _1288_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1288_argString, _1293_argExprString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1292_argIdents);
              _1289_i = (_1289_i) + (BigInteger.One);
            }
            RAST._IExpr _1294_onExpr;
            DCOMP._IOwnership _1295___v49;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1296_enclosingIdents;
            RAST._IExpr _out129;
            DCOMP._IOwnership _out130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
            (this).GenExpr(_1279_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out129, out _out130, out _out131);
            _1294_onExpr = _out129;
            _1295___v49 = _out130;
            _1296_enclosingIdents = _out131;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1296_enclosingIdents);
            Dafny.ISequence<Dafny.Rune> _1297_enclosingString;
            _1297_enclosingString = (_1294_onExpr)._ToString(DCOMP.__default.IND);
            DAST._IExpression _source57 = _1279_on;
            bool unmatched57 = true;
            if (unmatched57) {
              if (_source57.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1298___v50 = _source57.dtor_Companion_i_a0;
                unmatched57 = false;
                {
                  _1297_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_1297_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
                }
              }
            }
            if (unmatched57) {
              DAST._IExpression _1299___v51 = _source57;
              unmatched57 = false;
              {
                _1297_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1297_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
              }
            }
            Dafny.ISequence<Dafny.Rune> _1300_receiver;
            _1300_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source58 = _1283_maybeOutVars;
            bool unmatched58 = true;
            if (unmatched58) {
              if (_source58.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1301_outVars = _source58.dtor_value;
                unmatched58 = false;
                {
                  if ((new BigInteger((_1301_outVars).Count)) > (BigInteger.One)) {
                    _1300_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
                  }
                  BigInteger _1302_outI;
                  _1302_outI = BigInteger.Zero;
                  while ((_1302_outI) < (new BigInteger((_1301_outVars).Count))) {
                    if ((_1302_outI).Sign == 1) {
                      _1300_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_1300_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                    }
                    Dafny.ISequence<Dafny.Rune> _1303_outVar;
                    _1303_outVar = (_1301_outVars).Select(_1302_outI);
                    _1300_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_1300_receiver, (_1303_outVar));
                    _1302_outI = (_1302_outI) + (BigInteger.One);
                  }
                  if ((new BigInteger((_1301_outVars).Count)) > (BigInteger.One)) {
                    _1300_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_1300_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  }
                }
              }
            }
            if (unmatched58) {
              unmatched58 = false;
            }
            Dafny.ISequence<Dafny.Rune> _1304_renderedName;
            _1304_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source59 = _1280_name;
              bool unmatched59 = true;
              if (unmatched59) {
                if (_source59.is_Name) {
                  Dafny.ISequence<Dafny.Rune> _1305_name = _source59.dtor_name;
                  unmatched59 = false;
                  return DCOMP.__default.escapeIdent(_1305_name);
                }
              }
              if (unmatched59) {
                bool disjunctiveMatch9 = false;
                if (_source59.is_MapBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (_source59.is_SetBuilderAdd) {
                  disjunctiveMatch9 = true;
                }
                if (disjunctiveMatch9) {
                  unmatched59 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched59) {
                bool disjunctiveMatch10 = false;
                disjunctiveMatch10 = true;
                disjunctiveMatch10 = true;
                if (disjunctiveMatch10) {
                  unmatched59 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_1300_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_1300_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _1297_enclosingString), _1304_renderedName), _1284_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1288_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");")));
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_Return) {
          DAST._IExpression _1306_expr = _source55.dtor_expr;
          unmatched55 = false;
          {
            RAST._IExpr _1307_expr;
            DCOMP._IOwnership _1308___v52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1309_recIdents;
            RAST._IExpr _out132;
            DCOMP._IOwnership _out133;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
            (this).GenExpr(_1306_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out132, out _out133, out _out134);
            _1307_expr = _out132;
            _1308___v52 = _out133;
            _1309_recIdents = _out134;
            readIdents = _1309_recIdents;
            if (isLast) {
              generated = _1307_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1307_expr));
            }
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_EarlyReturn) {
          unmatched55 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      }
      if (unmatched55) {
        if (_source55.is_Halt) {
          unmatched55 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      }
      if (unmatched55) {
        DAST._IExpression _1310_e = _source55.dtor_Print_i_a0;
        unmatched55 = false;
        {
          RAST._IExpr _1311_printedExpr;
          DCOMP._IOwnership _1312_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1313_recIdents;
          RAST._IExpr _out135;
          DCOMP._IOwnership _out136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
          (this).GenExpr(_1310_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out135, out _out136, out _out137);
          _1311_printedExpr = _out135;
          _1312_recOwnership = _out136;
          _1313_recIdents = _out137;
          Dafny.ISequence<Dafny.Rune> _1314_printedExprString;
          _1314_printedExprString = (_1311_printedExpr)._ToString(DCOMP.__default.IND);
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), _1314_printedExprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));")));
          readIdents = _1313_recIdents;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source60 = range;
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_NoRange) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched60) {
        if (_source60.is_U8) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched60) {
        if (_source60.is_U16) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched60) {
        if (_source60.is_U32) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched60) {
        if (_source60.is_U64) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched60) {
        if (_source60.is_U128) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched60) {
        if (_source60.is_I8) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched60) {
        if (_source60.is_I16) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched60) {
        if (_source60.is_I32) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched60) {
        if (_source60.is_I64) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched60) {
        if (_source60.is_I128) {
          unmatched60 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched60) {
        DAST._INewtypeRange _1315___v53 = _source60;
        unmatched60 = false;
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
      throw new System.Exception("unexpected control point");
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
      DAST._IExpression _source61 = e;
      bool unmatched61 = true;
      if (unmatched61) {
        if (_source61.is_Literal) {
          DAST._ILiteral _h150 = _source61.dtor_Literal_i_a0;
          if (_h150.is_BoolLiteral) {
            bool _h200 = _h150.dtor_BoolLiteral_i_a0;
            if ((_h200) == (false)) {
              unmatched61 = false;
              {
                RAST._IExpr _out140;
                DCOMP._IOwnership _out141;
                DCOMP.COMP.FromOwned(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")), expectedOwnership, out _out140, out _out141);
                r = _out140;
                resultingOwnership = _out141;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                return ;
              }
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Literal) {
          DAST._ILiteral _h151 = _source61.dtor_Literal_i_a0;
          if (_h151.is_BoolLiteral) {
            bool _h201 = _h151.dtor_BoolLiteral_i_a0;
            if ((_h201) == (true)) {
              unmatched61 = false;
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
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Literal) {
          DAST._ILiteral _h152 = _source61.dtor_Literal_i_a0;
          if (_h152.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1316_i = _h152.dtor_IntLiteral_i_a0;
            DAST._IType _1317_t = _h152.dtor_IntLiteral_i_a1;
            unmatched61 = false;
            {
              DAST._IType _source62 = _1317_t;
              bool unmatched62 = true;
              if (unmatched62) {
                if (_source62.is_Primitive) {
                  DAST._IPrimitive _h80 = _source62.dtor_Primitive_i_a0;
                  if (_h80.is_Int) {
                    unmatched62 = false;
                    {
                      if ((new BigInteger((_1316_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(RAST.Expr.create_LiteralInt(_1316_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(RAST.Expr.create_LiteralString(_1316_i, true));
                      }
                    }
                  }
                }
              }
              if (unmatched62) {
                DAST._IType _1318_o = _source62;
                unmatched62 = false;
                {
                  RAST._IType _1319_genType;
                  RAST._IType _out144;
                  _out144 = (this).GenType(_1318_o, false, false);
                  _1319_genType = _out144;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1316_i), _1319_genType);
                }
              }
              RAST._IExpr _out145;
              DCOMP._IOwnership _out146;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out145, out _out146);
              r = _out145;
              resultingOwnership = _out146;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Literal) {
          DAST._ILiteral _h153 = _source61.dtor_Literal_i_a0;
          if (_h153.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1320_n = _h153.dtor_DecLiteral_i_a0;
            Dafny.ISequence<Dafny.Rune> _1321_d = _h153.dtor_DecLiteral_i_a1;
            DAST._IType _1322_t = _h153.dtor_DecLiteral_i_a2;
            unmatched61 = false;
            {
              DAST._IType _source63 = _1322_t;
              bool unmatched63 = true;
              if (unmatched63) {
                if (_source63.is_Primitive) {
                  DAST._IPrimitive _h81 = _source63.dtor_Primitive_i_a0;
                  if (_h81.is_Real) {
                    unmatched63 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1320_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1321_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched63) {
                DAST._IType _1323_o = _source63;
                unmatched63 = false;
                {
                  RAST._IType _1324_genType;
                  RAST._IType _out147;
                  _out147 = (this).GenType(_1323_o, false, false);
                  _1324_genType = _out147;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1320_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1321_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1324_genType);
                }
              }
              RAST._IExpr _out148;
              DCOMP._IOwnership _out149;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out148, out _out149);
              r = _out148;
              resultingOwnership = _out149;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Literal) {
          DAST._ILiteral _h154 = _source61.dtor_Literal_i_a0;
          if (_h154.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1325_l = _h154.dtor_StringLiteral_i_a0;
            unmatched61 = false;
            {
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1325_l, false));
              RAST._IExpr _out150;
              DCOMP._IOwnership _out151;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out150, out _out151);
              r = _out150;
              resultingOwnership = _out151;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Literal) {
          DAST._ILiteral _h155 = _source61.dtor_Literal_i_a0;
          if (_h155.is_CharLiteral) {
            Dafny.Rune _1326_c = _h155.dtor_CharLiteral_i_a0;
            unmatched61 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1326_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out152;
              DCOMP._IOwnership _out153;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out152, out _out153);
              r = _out152;
              resultingOwnership = _out153;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched61) {
        DAST._ILiteral _h156 = _source61.dtor_Literal_i_a0;
        DAST._IType _1327_tpe = _h156.dtor_Null_i_a0;
        unmatched61 = false;
        {
          RAST._IType _1328_tpeGen;
          RAST._IType _out154;
          _out154 = (this).GenType(_1327_tpe, false, false);
          _1328_tpeGen = _out154;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _1328_tpeGen);
          RAST._IExpr _out155;
          DCOMP._IOwnership _out156;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out155, out _out156);
          r = _out155;
          resultingOwnership = _out156;
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
      DAST._IBinOp _1329_op = _let_tmp_rhs49.dtor_op;
      DAST._IExpression _1330_lExpr = _let_tmp_rhs49.dtor_left;
      DAST._IExpression _1331_rExpr = _let_tmp_rhs49.dtor_right;
      DAST.Format._IBinaryOpFormat _1332_format = _let_tmp_rhs49.dtor_format2;
      bool _1333_becomesLeftCallsRight;
      _1333_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source64 = _1329_op;
        bool unmatched64 = true;
        if (unmatched64) {
          bool disjunctiveMatch11 = false;
          if (_source64.is_SetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_SetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_SetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_SetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_MapMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_MapSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_MultisetMerge) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_MultisetSubtraction) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_MultisetIntersection) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_MultisetDisjoint) {
            disjunctiveMatch11 = true;
          }
          if (_source64.is_Concat) {
            disjunctiveMatch11 = true;
          }
          if (disjunctiveMatch11) {
            unmatched64 = false;
            return true;
          }
        }
        if (unmatched64) {
          DAST._IBinOp _1334___v54 = _source64;
          unmatched64 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1335_becomesRightCallsLeft;
      _1335_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source65 = _1329_op;
        bool unmatched65 = true;
        if (unmatched65) {
          if (_source65.is_In) {
            unmatched65 = false;
            return true;
          }
        }
        if (unmatched65) {
          DAST._IBinOp _1336___v55 = _source65;
          unmatched65 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1337_becomesCallLeftRight;
      _1337_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source66 = _1329_op;
        bool unmatched66 = true;
        if (unmatched66) {
          if (_source66.is_Eq) {
            bool referential0 = _source66.dtor_referential;
            if ((referential0) == (true)) {
              bool nullable0 = _source66.dtor_nullable;
              if ((nullable0) == (false)) {
                unmatched66 = false;
                return true;
              }
            }
          }
        }
        if (unmatched66) {
          DAST._IBinOp _1338___v56 = _source66;
          unmatched66 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1339_expectedLeftOwnership;
      _1339_expectedLeftOwnership = ((_1333_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1335_becomesRightCallsLeft) || (_1337_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1340_expectedRightOwnership;
      _1340_expectedRightOwnership = (((_1333_becomesLeftCallsRight) || (_1337_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1335_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1341_left;
      DCOMP._IOwnership _1342___v57;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1343_recIdentsL;
      RAST._IExpr _out157;
      DCOMP._IOwnership _out158;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
      (this).GenExpr(_1330_lExpr, selfIdent, @params, _1339_expectedLeftOwnership, out _out157, out _out158, out _out159);
      _1341_left = _out157;
      _1342___v57 = _out158;
      _1343_recIdentsL = _out159;
      RAST._IExpr _1344_right;
      DCOMP._IOwnership _1345___v58;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1346_recIdentsR;
      RAST._IExpr _out160;
      DCOMP._IOwnership _out161;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
      (this).GenExpr(_1331_rExpr, selfIdent, @params, _1340_expectedRightOwnership, out _out160, out _out161, out _out162);
      _1344_right = _out160;
      _1345___v58 = _out161;
      _1346_recIdentsR = _out162;
      DAST._IBinOp _source67 = _1329_op;
      bool unmatched67 = true;
      if (unmatched67) {
        if (_source67.is_In) {
          unmatched67 = false;
          {
            r = ((_1344_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1341_left);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_SeqProperPrefix) {
          unmatched67 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1341_left, _1344_right, _1332_format);
        }
      }
      if (unmatched67) {
        if (_source67.is_SeqPrefix) {
          unmatched67 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1341_left, _1344_right, _1332_format);
        }
      }
      if (unmatched67) {
        if (_source67.is_SetMerge) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_SetSubtraction) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_SetIntersection) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_Subset) {
          unmatched67 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1341_left, _1344_right, _1332_format);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_ProperSubset) {
          unmatched67 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1341_left, _1344_right, _1332_format);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_SetDisjoint) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_MapMerge) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_MapSubtraction) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_MultisetMerge) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_MultisetSubtraction) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_MultisetIntersection) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_Submultiset) {
          unmatched67 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1341_left, _1344_right, _1332_format);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_ProperSubmultiset) {
          unmatched67 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1341_left, _1344_right, _1332_format);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_MultisetDisjoint) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_Concat) {
          unmatched67 = false;
          {
            r = ((_1341_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1344_right);
          }
        }
      }
      if (unmatched67) {
        DAST._IBinOp _1347___v59 = _source67;
        unmatched67 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1329_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1329_op), _1341_left, _1344_right, _1332_format);
          } else {
            DAST._IBinOp _source68 = _1329_op;
            bool unmatched68 = true;
            if (unmatched68) {
              if (_source68.is_Eq) {
                bool _1348_referential = _source68.dtor_referential;
                bool _1349_nullable = _source68.dtor_nullable;
                unmatched68 = false;
                {
                  if (_1348_referential) {
                    if (_1349_nullable) {
                      r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_1341_left, _1344_right));
                    } else {
                      r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_1341_left, _1344_right));
                    }
                  } else {
                    r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1341_left, _1344_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
            if (unmatched68) {
              if (_source68.is_EuclidianDiv) {
                unmatched68 = false;
                {
                  r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_1341_left, _1344_right));
                }
              }
            }
            if (unmatched68) {
              if (_source68.is_EuclidianMod) {
                unmatched68 = false;
                {
                  r = RAST.Expr.create_Call(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_1341_left, _1344_right));
                }
              }
            }
            if (unmatched68) {
              Dafny.ISequence<Dafny.Rune> _1350_op = _source68.dtor_Passthrough_i_a0;
              unmatched68 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1350_op, _1341_left, _1344_right, _1332_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out163;
      DCOMP._IOwnership _out164;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out163, out _out164);
      r = _out163;
      resultingOwnership = _out164;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1343_recIdentsL, _1346_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs50 = e;
      DAST._IExpression _1351_expr = _let_tmp_rhs50.dtor_value;
      DAST._IType _1352_fromTpe = _let_tmp_rhs50.dtor_from;
      DAST._IType _1353_toTpe = _let_tmp_rhs50.dtor_typ;
      RAST._IExpr _1354_recursiveGen;
      DCOMP._IOwnership _1355_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1356_recIdents;
      RAST._IExpr _out165;
      DCOMP._IOwnership _out166;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out167;
      (this).GenExpr(_1351_expr, selfIdent, @params, expectedOwnership, out _out165, out _out166, out _out167);
      _1354_recursiveGen = _out165;
      _1355_recOwned = _out166;
      _1356_recIdents = _out167;
      r = _1354_recursiveGen;
      if (object.Equals(_1355_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out168;
      DCOMP._IOwnership _out169;
      DCOMP.COMP.FromOwnership(r, _1355_recOwned, expectedOwnership, out _out168, out _out169);
      r = _out168;
      resultingOwnership = _out169;
      readIdents = _1356_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs51 = e;
      DAST._IExpression _1357_expr = _let_tmp_rhs51.dtor_value;
      DAST._IType _1358_fromTpe = _let_tmp_rhs51.dtor_from;
      DAST._IType _1359_toTpe = _let_tmp_rhs51.dtor_typ;
      RAST._IExpr _1360_recursiveGen;
      DCOMP._IOwnership _1361_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1362_recIdents;
      RAST._IExpr _out170;
      DCOMP._IOwnership _out171;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
      (this).GenExpr(_1357_expr, selfIdent, @params, expectedOwnership, out _out170, out _out171, out _out172);
      _1360_recursiveGen = _out170;
      _1361_recOwned = _out171;
      _1362_recIdents = _out172;
      r = _1360_recursiveGen;
      if (object.Equals(_1361_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out173;
      DCOMP._IOwnership _out174;
      DCOMP.COMP.FromOwnership(r, _1361_recOwned, expectedOwnership, out _out173, out _out174);
      r = _out173;
      resultingOwnership = _out174;
      readIdents = _1362_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs52 = e;
      DAST._IExpression _1363_expr = _let_tmp_rhs52.dtor_value;
      DAST._IType _1364_fromTpe = _let_tmp_rhs52.dtor_from;
      DAST._IType _1365_toTpe = _let_tmp_rhs52.dtor_typ;
      DAST._IType _let_tmp_rhs53 = _1365_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1366___v60 = _let_tmp_rhs53.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _1367___v61 = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs54 = _let_tmp_rhs53.dtor_resolved;
      DAST._IType _1368_b = _let_tmp_rhs54.dtor_baseType;
      DAST._INewtypeRange _1369_range = _let_tmp_rhs54.dtor_range;
      bool _1370_erase = _let_tmp_rhs54.dtor_erase;
      if (object.Equals(_1364_fromTpe, _1368_b)) {
        RAST._IExpr _1371_recursiveGen;
        DCOMP._IOwnership _1372_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1373_recIdents;
        RAST._IExpr _out175;
        DCOMP._IOwnership _out176;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
        (this).GenExpr(_1363_expr, selfIdent, @params, expectedOwnership, out _out175, out _out176, out _out177);
        _1371_recursiveGen = _out175;
        _1372_recOwned = _out176;
        _1373_recIdents = _out177;
        Std.Wrappers._IOption<RAST._IType> _1374_potentialRhsType;
        _1374_potentialRhsType = DCOMP.COMP.NewtypeToRustType(_1368_b, _1369_range);
        Std.Wrappers._IOption<RAST._IType> _source69 = _1374_potentialRhsType;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_Some) {
            RAST._IType _1375_v = _source69.dtor_value;
            unmatched69 = false;
            r = RAST.Expr.create_ConversionNum(_1375_v, _1371_recursiveGen);
            RAST._IExpr _out178;
            DCOMP._IOwnership _out179;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out178, out _out179);
            r = _out178;
            resultingOwnership = _out179;
          }
        }
        if (unmatched69) {
          unmatched69 = false;
          if (_1370_erase) {
            r = _1371_recursiveGen;
          } else {
            RAST._IType _1376_rhsType;
            RAST._IType _out180;
            _out180 = (this).GenType(_1365_toTpe, true, false);
            _1376_rhsType = _out180;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1376_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1371_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out181;
          DCOMP._IOwnership _out182;
          DCOMP.COMP.FromOwnership(r, _1372_recOwned, expectedOwnership, out _out181, out _out182);
          r = _out181;
          resultingOwnership = _out182;
        }
        readIdents = _1373_recIdents;
      } else {
        RAST._IExpr _out183;
        DCOMP._IOwnership _out184;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out185;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1363_expr, _1364_fromTpe, _1368_b), _1368_b, _1365_toTpe), selfIdent, @params, expectedOwnership, out _out183, out _out184, out _out185);
        r = _out183;
        resultingOwnership = _out184;
        readIdents = _out185;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1377_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1378_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1379_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1378_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1380___v62 = _let_tmp_rhs56.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _1381___v63 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _1382_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1383_range = _let_tmp_rhs57.dtor_range;
      bool _1384_erase = _let_tmp_rhs57.dtor_erase;
      if (object.Equals(_1382_b, _1379_toTpe)) {
        RAST._IExpr _1385_recursiveGen;
        DCOMP._IOwnership _1386_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1387_recIdents;
        RAST._IExpr _out186;
        DCOMP._IOwnership _out187;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
        (this).GenExpr(_1377_expr, selfIdent, @params, expectedOwnership, out _out186, out _out187, out _out188);
        _1385_recursiveGen = _out186;
        _1386_recOwned = _out187;
        _1387_recIdents = _out188;
        if (_1384_erase) {
          r = _1385_recursiveGen;
        } else {
          r = (_1385_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
        }
        RAST._IExpr _out189;
        DCOMP._IOwnership _out190;
        DCOMP.COMP.FromOwnership(r, _1386_recOwned, expectedOwnership, out _out189, out _out190);
        r = _out189;
        resultingOwnership = _out190;
        readIdents = _1387_recIdents;
      } else {
        RAST._IExpr _out191;
        DCOMP._IOwnership _out192;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1377_expr, _1378_fromTpe, _1382_b), _1382_b, _1379_toTpe), selfIdent, @params, expectedOwnership, out _out191, out _out192, out _out193);
        r = _out191;
        resultingOwnership = _out192;
        readIdents = _out193;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _1388_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1389_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1390_toTpe = _let_tmp_rhs58.dtor_typ;
      RAST._IExpr _1391_recursiveGen;
      DCOMP._IOwnership _1392_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1393_recIdents;
      RAST._IExpr _out194;
      DCOMP._IOwnership _out195;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out196;
      (this).GenExpr(_1388_expr, selfIdent, @params, expectedOwnership, out _out194, out _out195, out _out196);
      _1391_recursiveGen = _out194;
      _1392_recOwned = _out195;
      _1393_recIdents = _out196;
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1391_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)")));
      RAST._IExpr _out197;
      DCOMP._IOwnership _out198;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out197, out _out198);
      r = _out197;
      resultingOwnership = _out198;
      readIdents = _1393_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs59 = e;
      DAST._IExpression _1394_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1395_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1396_toTpe = _let_tmp_rhs59.dtor_typ;
      if (object.Equals(_1395_fromTpe, _1396_toTpe)) {
        RAST._IExpr _1397_recursiveGen;
        DCOMP._IOwnership _1398_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1399_recIdents;
        RAST._IExpr _out199;
        DCOMP._IOwnership _out200;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
        (this).GenExpr(_1394_expr, selfIdent, @params, expectedOwnership, out _out199, out _out200, out _out201);
        _1397_recursiveGen = _out199;
        _1398_recOwned = _out200;
        _1399_recIdents = _out201;
        r = _1397_recursiveGen;
        RAST._IExpr _out202;
        DCOMP._IOwnership _out203;
        DCOMP.COMP.FromOwnership(r, _1398_recOwned, expectedOwnership, out _out202, out _out203);
        r = _out202;
        resultingOwnership = _out203;
        readIdents = _1399_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source70 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1395_fromTpe, _1396_toTpe);
        bool unmatched70 = true;
        if (unmatched70) {
          DAST._IType _00 = _source70.dtor__0;
          if (_00.is_Nullable) {
            DAST._IType _1400___v64 = _00.dtor_Nullable_i_a0;
            DAST._IType _1401___v65 = _source70.dtor__1;
            unmatched70 = false;
            {
              RAST._IExpr _out204;
              DCOMP._IOwnership _out205;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out206;
              (this).GenExprConvertFromNullable(e, selfIdent, @params, expectedOwnership, out _out204, out _out205, out _out206);
              r = _out204;
              resultingOwnership = _out205;
              readIdents = _out206;
            }
          }
        }
        if (unmatched70) {
          DAST._IType _1402___v66 = _source70.dtor__0;
          DAST._IType _10 = _source70.dtor__1;
          if (_10.is_Nullable) {
            DAST._IType _1403___v67 = _10.dtor_Nullable_i_a0;
            unmatched70 = false;
            {
              RAST._IExpr _out207;
              DCOMP._IOwnership _out208;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
              (this).GenExprConvertToNullable(e, selfIdent, @params, expectedOwnership, out _out207, out _out208, out _out209);
              r = _out207;
              resultingOwnership = _out208;
              readIdents = _out209;
            }
          }
        }
        if (unmatched70) {
          DAST._IType _1404___v68 = _source70.dtor__0;
          DAST._IType _11 = _source70.dtor__1;
          if (_11.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1405___v69 = _11.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _1406___v70 = _11.dtor_typeArgs;
            DAST._IResolvedType resolved1 = _11.dtor_resolved;
            if (resolved1.is_Newtype) {
              DAST._IType _1407_b = resolved1.dtor_baseType;
              DAST._INewtypeRange _1408_range = resolved1.dtor_range;
              bool _1409_erase = resolved1.dtor_erase;
              unmatched70 = false;
              {
                RAST._IExpr _out210;
                DCOMP._IOwnership _out211;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out212;
                (this).GenExprConvertToNewtype(e, selfIdent, @params, expectedOwnership, out _out210, out _out211, out _out212);
                r = _out210;
                resultingOwnership = _out211;
                readIdents = _out212;
              }
            }
          }
        }
        if (unmatched70) {
          DAST._IType _01 = _source70.dtor__0;
          if (_01.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1410___v71 = _01.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _1411___v72 = _01.dtor_typeArgs;
            DAST._IResolvedType resolved2 = _01.dtor_resolved;
            if (resolved2.is_Newtype) {
              DAST._IType _1412_b = resolved2.dtor_baseType;
              DAST._INewtypeRange _1413_range = resolved2.dtor_range;
              bool _1414_erase = resolved2.dtor_erase;
              DAST._IType _1415___v73 = _source70.dtor__1;
              unmatched70 = false;
              {
                RAST._IExpr _out213;
                DCOMP._IOwnership _out214;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out215;
                (this).GenExprConvertFromNewtype(e, selfIdent, @params, expectedOwnership, out _out213, out _out214, out _out215);
                r = _out213;
                resultingOwnership = _out214;
                readIdents = _out215;
              }
            }
          }
        }
        if (unmatched70) {
          DAST._IType _02 = _source70.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h82 = _02.dtor_Primitive_i_a0;
            if (_h82.is_Int) {
              DAST._IType _12 = _source70.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h83 = _12.dtor_Primitive_i_a0;
                if (_h83.is_Real) {
                  unmatched70 = false;
                  {
                    RAST._IExpr _1416_recursiveGen;
                    DCOMP._IOwnership _1417___v74;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1418_recIdents;
                    RAST._IExpr _out216;
                    DCOMP._IOwnership _out217;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out218;
                    (this).GenExpr(_1394_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out216, out _out217, out _out218);
                    _1416_recursiveGen = _out216;
                    _1417___v74 = _out217;
                    _1418_recIdents = _out218;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1416_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out219;
                    DCOMP._IOwnership _out220;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out219, out _out220);
                    r = _out219;
                    resultingOwnership = _out220;
                    readIdents = _1418_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched70) {
          DAST._IType _03 = _source70.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h84 = _03.dtor_Primitive_i_a0;
            if (_h84.is_Real) {
              DAST._IType _13 = _source70.dtor__1;
              if (_13.is_Primitive) {
                DAST._IPrimitive _h85 = _13.dtor_Primitive_i_a0;
                if (_h85.is_Int) {
                  unmatched70 = false;
                  {
                    RAST._IExpr _1419_recursiveGen;
                    DCOMP._IOwnership _1420___v75;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1421_recIdents;
                    RAST._IExpr _out221;
                    DCOMP._IOwnership _out222;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out223;
                    (this).GenExpr(_1394_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out221, out _out222, out _out223);
                    _1419_recursiveGen = _out221;
                    _1420___v75 = _out222;
                    _1421_recIdents = _out223;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1419_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out224;
                    DCOMP._IOwnership _out225;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out224, out _out225);
                    r = _out224;
                    resultingOwnership = _out225;
                    readIdents = _1421_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched70) {
          DAST._IType _04 = _source70.dtor__0;
          if (_04.is_Primitive) {
            DAST._IPrimitive _h86 = _04.dtor_Primitive_i_a0;
            if (_h86.is_Int) {
              DAST._IType _14 = _source70.dtor__1;
              if (_14.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1422___v76 = _14.dtor_Passthrough_i_a0;
                unmatched70 = false;
                {
                  RAST._IType _1423_rhsType;
                  RAST._IType _out226;
                  _out226 = (this).GenType(_1396_toTpe, true, false);
                  _1423_rhsType = _out226;
                  RAST._IExpr _1424_recursiveGen;
                  DCOMP._IOwnership _1425___v77;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1426_recIdents;
                  RAST._IExpr _out227;
                  DCOMP._IOwnership _out228;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out229;
                  (this).GenExpr(_1394_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out227, out _out228, out _out229);
                  _1424_recursiveGen = _out227;
                  _1425___v77 = _out228;
                  _1426_recIdents = _out229;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1423_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1424_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out230;
                  DCOMP._IOwnership _out231;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out230, out _out231);
                  r = _out230;
                  resultingOwnership = _out231;
                  readIdents = _1426_recIdents;
                }
              }
            }
          }
        }
        if (unmatched70) {
          DAST._IType _05 = _source70.dtor__0;
          if (_05.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1427___v78 = _05.dtor_Passthrough_i_a0;
            DAST._IType _15 = _source70.dtor__1;
            if (_15.is_Primitive) {
              DAST._IPrimitive _h87 = _15.dtor_Primitive_i_a0;
              if (_h87.is_Int) {
                unmatched70 = false;
                {
                  RAST._IType _1428_rhsType;
                  RAST._IType _out232;
                  _out232 = (this).GenType(_1395_fromTpe, true, false);
                  _1428_rhsType = _out232;
                  RAST._IExpr _1429_recursiveGen;
                  DCOMP._IOwnership _1430___v79;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1431_recIdents;
                  RAST._IExpr _out233;
                  DCOMP._IOwnership _out234;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out235;
                  (this).GenExpr(_1394_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out233, out _out234, out _out235);
                  _1429_recursiveGen = _out233;
                  _1430___v79 = _out234;
                  _1431_recIdents = _out235;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_1429_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                  RAST._IExpr _out236;
                  DCOMP._IOwnership _out237;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out236, out _out237);
                  r = _out236;
                  resultingOwnership = _out237;
                  readIdents = _1431_recIdents;
                }
              }
            }
          }
        }
        if (unmatched70) {
          DAST._IType _06 = _source70.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h88 = _06.dtor_Primitive_i_a0;
            if (_h88.is_Int) {
              DAST._IType _16 = _source70.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h89 = _16.dtor_Primitive_i_a0;
                if (_h89.is_Char) {
                  unmatched70 = false;
                  {
                    RAST._IType _1432_rhsType;
                    RAST._IType _out238;
                    _out238 = (this).GenType(_1396_toTpe, true, false);
                    _1432_rhsType = _out238;
                    RAST._IExpr _1433_recursiveGen;
                    DCOMP._IOwnership _1434___v80;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1435_recIdents;
                    RAST._IExpr _out239;
                    DCOMP._IOwnership _out240;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
                    (this).GenExpr(_1394_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out239, out _out240, out _out241);
                    _1433_recursiveGen = _out239;
                    _1434___v80 = _out240;
                    _1435_recIdents = _out241;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_1433_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                    RAST._IExpr _out242;
                    DCOMP._IOwnership _out243;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out242, out _out243);
                    r = _out242;
                    resultingOwnership = _out243;
                    readIdents = _1435_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched70) {
          DAST._IType _07 = _source70.dtor__0;
          if (_07.is_Primitive) {
            DAST._IPrimitive _h810 = _07.dtor_Primitive_i_a0;
            if (_h810.is_Char) {
              DAST._IType _17 = _source70.dtor__1;
              if (_17.is_Primitive) {
                DAST._IPrimitive _h811 = _17.dtor_Primitive_i_a0;
                if (_h811.is_Int) {
                  unmatched70 = false;
                  {
                    RAST._IType _1436_rhsType;
                    RAST._IType _out244;
                    _out244 = (this).GenType(_1395_fromTpe, true, false);
                    _1436_rhsType = _out244;
                    RAST._IExpr _1437_recursiveGen;
                    DCOMP._IOwnership _1438___v81;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1439_recIdents;
                    RAST._IExpr _out245;
                    DCOMP._IOwnership _out246;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out247;
                    (this).GenExpr(_1394_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out245, out _out246, out _out247);
                    _1437_recursiveGen = _out245;
                    _1438___v81 = _out246;
                    _1439_recIdents = _out247;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::BigInt::from("), (_1437_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)}")));
                    RAST._IExpr _out248;
                    DCOMP._IOwnership _out249;
                    DCOMP.COMP.FromOwned(r, expectedOwnership, out _out248, out _out249);
                    r = _out248;
                    resultingOwnership = _out249;
                    readIdents = _1439_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched70) {
          DAST._IType _08 = _source70.dtor__0;
          if (_08.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1440___v82 = _08.dtor_Passthrough_i_a0;
            DAST._IType _18 = _source70.dtor__1;
            if (_18.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1441___v83 = _18.dtor_Passthrough_i_a0;
              unmatched70 = false;
              {
                RAST._IExpr _1442_recursiveGen;
                DCOMP._IOwnership _1443___v84;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1444_recIdents;
                RAST._IExpr _out250;
                DCOMP._IOwnership _out251;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out252;
                (this).GenExpr(_1394_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out250, out _out251, out _out252);
                _1442_recursiveGen = _out250;
                _1443___v84 = _out251;
                _1444_recIdents = _out252;
                RAST._IType _1445_toTpeGen;
                RAST._IType _out253;
                _out253 = (this).GenType(_1396_toTpe, true, false);
                _1445_toTpeGen = _out253;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1442_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1445_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out254;
                DCOMP._IOwnership _out255;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out254, out _out255);
                r = _out254;
                resultingOwnership = _out255;
                readIdents = _1444_recIdents;
              }
            }
          }
        }
        if (unmatched70) {
          _System._ITuple2<DAST._IType, DAST._IType> _1446___v85 = _source70;
          unmatched70 = false;
          {
            RAST._IExpr _out256;
            DCOMP._IOwnership _out257;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
            (this).GenExprConvertNotImplemented(e, selfIdent, @params, expectedOwnership, out _out256, out _out257, out _out258);
            r = _out256;
            resultingOwnership = _out257;
            readIdents = _out258;
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
      DAST._IExpression _source71 = e;
      bool unmatched71 = true;
      if (unmatched71) {
        if (_source71.is_Literal) {
          DAST._ILiteral _1447___v86 = _source71.dtor_Literal_i_a0;
          unmatched71 = false;
          RAST._IExpr _out259;
          DCOMP._IOwnership _out260;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
          (this).GenExprLiteral(e, selfIdent, @params, expectedOwnership, out _out259, out _out260, out _out261);
          r = _out259;
          resultingOwnership = _out260;
          readIdents = _out261;
        }
      }
      if (unmatched71) {
        if (_source71.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1448_name = _source71.dtor_Ident_i_a0;
          unmatched71 = false;
          {
            r = RAST.Expr.create_Identifier(DCOMP.__default.escapeIdent(_1448_name));
            bool _1449_currentlyBorrowed;
            _1449_currentlyBorrowed = (@params).Contains(_1448_name);
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
              r = RAST.__default.BorrowMut(r);
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              r = RAST.__default.Clone(r);
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else if (_1449_currentlyBorrowed) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else {
              r = RAST.__default.Borrow(r);
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1448_name);
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1450_path = _source71.dtor_Companion_i_a0;
          unmatched71 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1451_p;
            Dafny.ISequence<Dafny.Rune> _out262;
            _out262 = DCOMP.COMP.GenPath(_1450_path);
            _1451_p = _out262;
            r = RAST.Expr.create_RawExpr(_1451_p);
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out263, out _out264);
            r = _out263;
            resultingOwnership = _out264;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_InitializationValue) {
          DAST._IType _1452_typ = _source71.dtor_typ;
          unmatched71 = false;
          {
            RAST._IType _1453_typExpr;
            RAST._IType _out265;
            _out265 = (this).GenType(_1452_typ, false, false);
            _1453_typExpr = _out265;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1453_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            RAST._IExpr _out266;
            DCOMP._IOwnership _out267;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out266, out _out267);
            r = _out266;
            resultingOwnership = _out267;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1454_values = _source71.dtor_Tuple_i_a0;
          unmatched71 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1455_s;
            _1455_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1456_i;
            _1456_i = BigInteger.Zero;
            while ((_1456_i) < (new BigInteger((_1454_values).Count))) {
              if ((_1456_i).Sign == 1) {
                _1455_s = Dafny.Sequence<Dafny.Rune>.Concat(_1455_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
              }
              RAST._IExpr _1457_recursiveGen;
              DCOMP._IOwnership _1458___v87;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1459_recIdents;
              RAST._IExpr _out268;
              DCOMP._IOwnership _out269;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
              (this).GenExpr((_1454_values).Select(_1456_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out268, out _out269, out _out270);
              _1457_recursiveGen = _out268;
              _1458___v87 = _out269;
              _1459_recIdents = _out270;
              _1455_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1455_s, (_1457_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1459_recIdents);
              _1456_i = (_1456_i) + (BigInteger.One);
            }
            _1455_s = Dafny.Sequence<Dafny.Rune>.Concat(_1455_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            r = RAST.Expr.create_RawExpr(_1455_s);
            RAST._IExpr _out271;
            DCOMP._IOwnership _out272;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out271, out _out272);
            r = _out271;
            resultingOwnership = _out272;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1460_path = _source71.dtor_path;
          Dafny.ISequence<DAST._IType> _1461_typeArgs = _source71.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1462_args = _source71.dtor_args;
          unmatched71 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1463_path;
            Dafny.ISequence<Dafny.Rune> _out273;
            _out273 = DCOMP.COMP.GenPath(_1460_path);
            _1463_path = _out273;
            Dafny.ISequence<Dafny.Rune> _1464_s;
            _1464_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1463_path);
            if ((new BigInteger((_1461_typeArgs).Count)).Sign == 1) {
              BigInteger _1465_i;
              _1465_i = BigInteger.Zero;
              Dafny.ISequence<RAST._IType> _1466_typeExprs;
              _1466_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              while ((_1465_i) < (new BigInteger((_1461_typeArgs).Count))) {
                RAST._IType _1467_typeExpr;
                RAST._IType _out274;
                _out274 = (this).GenType((_1461_typeArgs).Select(_1465_i), false, false);
                _1467_typeExpr = _out274;
                _1466_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1466_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1467_typeExpr));
                _1465_i = (_1465_i) + (BigInteger.One);
              }
              _1464_s = Dafny.Sequence<Dafny.Rune>.Concat(_1464_s, (RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1466_typeExprs))._ToString(DCOMP.__default.IND));
            }
            _1464_s = Dafny.Sequence<Dafny.Rune>.Concat(_1464_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1468_i;
            _1468_i = BigInteger.Zero;
            while ((_1468_i) < (new BigInteger((_1462_args).Count))) {
              if ((_1468_i).Sign == 1) {
                _1464_s = Dafny.Sequence<Dafny.Rune>.Concat(_1464_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              RAST._IExpr _1469_recursiveGen;
              DCOMP._IOwnership _1470___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1471_recIdents;
              RAST._IExpr _out275;
              DCOMP._IOwnership _out276;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
              (this).GenExpr((_1462_args).Select(_1468_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out275, out _out276, out _out277);
              _1469_recursiveGen = _out275;
              _1470___v88 = _out276;
              _1471_recIdents = _out277;
              _1464_s = Dafny.Sequence<Dafny.Rune>.Concat(_1464_s, (_1469_recursiveGen)._ToString(DCOMP.__default.IND));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1471_recIdents);
              _1468_i = (_1468_i) + (BigInteger.One);
            }
            _1464_s = Dafny.Sequence<Dafny.Rune>.Concat(_1464_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
            r = RAST.Expr.create_RawExpr(_1464_s);
            RAST._IExpr _out278;
            DCOMP._IOwnership _out279;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out278, out _out279);
            r = _out278;
            resultingOwnership = _out279;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _1472_dims = _source71.dtor_dims;
          DAST._IType _1473_typ = _source71.dtor_typ;
          unmatched71 = false;
          {
            BigInteger _1474_i;
            _1474_i = (new BigInteger((_1472_dims).Count)) - (BigInteger.One);
            RAST._IType _1475_genTyp;
            RAST._IType _out280;
            _out280 = (this).GenType(_1473_typ, false, false);
            _1475_genTyp = _out280;
            Dafny.ISequence<Dafny.Rune> _1476_s;
            _1476_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1475_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            while ((_1474_i).Sign != -1) {
              RAST._IExpr _1477_recursiveGen;
              DCOMP._IOwnership _1478___v89;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1479_recIdents;
              RAST._IExpr _out281;
              DCOMP._IOwnership _out282;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out283;
              (this).GenExpr((_1472_dims).Select(_1474_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out281, out _out282, out _out283);
              _1477_recursiveGen = _out281;
              _1478___v89 = _out282;
              _1479_recIdents = _out283;
              _1476_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _1476_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_1477_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1479_recIdents);
              _1474_i = (_1474_i) - (BigInteger.One);
            }
            r = RAST.Expr.create_RawExpr(_1476_s);
            RAST._IExpr _out284;
            DCOMP._IOwnership _out285;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out284, out _out285);
            r = _out284;
            resultingOwnership = _out285;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1480_path = _source71.dtor_path;
          Dafny.ISequence<DAST._IType> _1481_typeArgs = _source71.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1482_variant = _source71.dtor_variant;
          bool _1483_isCo = _source71.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1484_values = _source71.dtor_contents;
          unmatched71 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1485_path;
            Dafny.ISequence<Dafny.Rune> _out286;
            _out286 = DCOMP.COMP.GenPath(_1480_path);
            _1485_path = _out286;
            Dafny.ISequence<Dafny.Rune> _1486_s;
            _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1485_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            if ((new BigInteger((_1481_typeArgs).Count)).Sign == 1) {
              _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
              BigInteger _1487_i;
              _1487_i = BigInteger.Zero;
              while ((_1487_i) < (new BigInteger((_1481_typeArgs).Count))) {
                if ((_1487_i).Sign == 1) {
                  _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _1488_typeExpr;
                RAST._IType _out287;
                _out287 = (this).GenType((_1481_typeArgs).Select(_1487_i), false, false);
                _1488_typeExpr = _out287;
                _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, (_1488_typeExpr)._ToString(DCOMP.__default.IND));
                _1487_i = (_1487_i) + (BigInteger.One);
              }
              _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::"));
            }
            _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, DCOMP.__default.escapeIdent(_1482_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1489_i;
            _1489_i = BigInteger.Zero;
            _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
            while ((_1489_i) < (new BigInteger((_1484_values).Count))) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs60 = (_1484_values).Select(_1489_i);
              Dafny.ISequence<Dafny.Rune> _1490_name = _let_tmp_rhs60.dtor__0;
              DAST._IExpression _1491_value = _let_tmp_rhs60.dtor__1;
              if ((_1489_i).Sign == 1) {
                _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1483_isCo) {
                RAST._IExpr _1492_recursiveGen;
                DCOMP._IOwnership _1493___v90;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1494_recIdents;
                RAST._IExpr _out288;
                DCOMP._IOwnership _out289;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                (this).GenExpr(_1491_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), DCOMP.Ownership.create_OwnershipOwned(), out _out288, out _out289, out _out290);
                _1492_recursiveGen = _out288;
                _1493___v90 = _out289;
                _1494_recIdents = _out290;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1494_recIdents);
                Dafny.ISequence<Dafny.Rune> _1495_allReadCloned;
                _1495_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1494_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1496_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1494_recIdents).Elements) {
                    _1496_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1494_recIdents).Contains(_1496_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 2844)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1495_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1495_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent(_1496_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), DCOMP.__default.escapeIdent(_1496_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1494_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1494_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1496_next));
                }
                _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, DCOMP.__default.escapeIdent(_1490_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _1495_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1492_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
              } else {
                RAST._IExpr _1497_recursiveGen;
                DCOMP._IOwnership _1498___v91;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1499_recIdents;
                RAST._IExpr _out291;
                DCOMP._IOwnership _out292;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out293;
                (this).GenExpr(_1491_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out291, out _out292, out _out293);
                _1497_recursiveGen = _out291;
                _1498___v91 = _out292;
                _1499_recIdents = _out293;
                _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, DCOMP.__default.escapeIdent(_1490_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1497_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1499_recIdents);
              }
              _1489_i = (_1489_i) + (BigInteger.One);
            }
            _1486_s = Dafny.Sequence<Dafny.Rune>.Concat(_1486_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
            r = RAST.Expr.create_RawExpr(_1486_s);
            RAST._IExpr _out294;
            DCOMP._IOwnership _out295;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out294, out _out295);
            r = _out294;
            resultingOwnership = _out295;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Convert) {
          DAST._IExpression _1500___v92 = _source71.dtor_value;
          DAST._IType _1501___v93 = _source71.dtor_from;
          DAST._IType _1502___v94 = _source71.dtor_typ;
          unmatched71 = false;
          {
            RAST._IExpr _out296;
            DCOMP._IOwnership _out297;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
            (this).GenExprConvert(e, selfIdent, @params, expectedOwnership, out _out296, out _out297, out _out298);
            r = _out296;
            resultingOwnership = _out297;
            readIdents = _out298;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SeqConstruct) {
          DAST._IExpression _1503_length = _source71.dtor_length;
          DAST._IExpression _1504_expr = _source71.dtor_elem;
          unmatched71 = false;
          {
            RAST._IExpr _1505_recursiveGen;
            DCOMP._IOwnership _1506___v95;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1507_recIdents;
            RAST._IExpr _out299;
            DCOMP._IOwnership _out300;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
            (this).GenExpr(_1504_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out299, out _out300, out _out301);
            _1505_recursiveGen = _out299;
            _1506___v95 = _out300;
            _1507_recIdents = _out301;
            RAST._IExpr _1508_lengthGen;
            DCOMP._IOwnership _1509___v96;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1510_lengthIdents;
            RAST._IExpr _out302;
            DCOMP._IOwnership _out303;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
            (this).GenExpr(_1503_length, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out302, out _out303, out _out304);
            _1508_lengthGen = _out302;
            _1509___v96 = _out303;
            _1510_lengthIdents = _out304;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1505_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1508_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer.0(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1507_recIdents, _1510_lengthIdents);
            RAST._IExpr _out305;
            DCOMP._IOwnership _out306;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out305, out _out306);
            r = _out305;
            resultingOwnership = _out306;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1511_exprs = _source71.dtor_elements;
          DAST._IType _1512_typ = _source71.dtor_typ;
          unmatched71 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1513_genTpe;
            RAST._IType _out307;
            _out307 = (this).GenType(_1512_typ, false, false);
            _1513_genTpe = _out307;
            BigInteger _1514_i;
            _1514_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1515_args;
            _1515_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1514_i) < (new BigInteger((_1511_exprs).Count))) {
              RAST._IExpr _1516_recursiveGen;
              DCOMP._IOwnership _1517___v97;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1518_recIdents;
              RAST._IExpr _out308;
              DCOMP._IOwnership _out309;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out310;
              (this).GenExpr((_1511_exprs).Select(_1514_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out308, out _out309, out _out310);
              _1516_recursiveGen = _out308;
              _1517___v97 = _out309;
              _1518_recIdents = _out310;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1518_recIdents);
              _1515_args = Dafny.Sequence<RAST._IExpr>.Concat(_1515_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1516_recursiveGen));
              _1514_i = (_1514_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _1515_args);
            if ((new BigInteger((_1515_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1513_genTpe));
            }
            RAST._IExpr _out311;
            DCOMP._IOwnership _out312;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out311, out _out312);
            r = _out311;
            resultingOwnership = _out312;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1519_exprs = _source71.dtor_elements;
          unmatched71 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1520_generatedValues;
            _1520_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1521_i;
            _1521_i = BigInteger.Zero;
            while ((_1521_i) < (new BigInteger((_1519_exprs).Count))) {
              RAST._IExpr _1522_recursiveGen;
              DCOMP._IOwnership _1523___v98;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1524_recIdents;
              RAST._IExpr _out313;
              DCOMP._IOwnership _out314;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
              (this).GenExpr((_1519_exprs).Select(_1521_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out313, out _out314, out _out315);
              _1522_recursiveGen = _out313;
              _1523___v98 = _out314;
              _1524_recIdents = _out315;
              _1520_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1520_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1522_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1524_recIdents);
              _1521_i = (_1521_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _1520_generatedValues);
            RAST._IExpr _out316;
            DCOMP._IOwnership _out317;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out316, out _out317);
            r = _out316;
            resultingOwnership = _out317;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1525_exprs = _source71.dtor_elements;
          unmatched71 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1526_generatedValues;
            _1526_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1527_i;
            _1527_i = BigInteger.Zero;
            while ((_1527_i) < (new BigInteger((_1525_exprs).Count))) {
              RAST._IExpr _1528_recursiveGen;
              DCOMP._IOwnership _1529___v99;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1530_recIdents;
              RAST._IExpr _out318;
              DCOMP._IOwnership _out319;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
              (this).GenExpr((_1525_exprs).Select(_1527_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
              _1528_recursiveGen = _out318;
              _1529___v99 = _out319;
              _1530_recIdents = _out320;
              _1526_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1526_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1528_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1530_recIdents);
              _1527_i = (_1527_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _1526_generatedValues);
            RAST._IExpr _out321;
            DCOMP._IOwnership _out322;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out321, out _out322);
            r = _out321;
            resultingOwnership = _out322;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_ToMultiset) {
          DAST._IExpression _1531_expr = _source71.dtor_ToMultiset_i_a0;
          unmatched71 = false;
          {
            RAST._IExpr _1532_recursiveGen;
            DCOMP._IOwnership _1533___v100;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1534_recIdents;
            RAST._IExpr _out323;
            DCOMP._IOwnership _out324;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out325;
            (this).GenExpr(_1531_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out323, out _out324, out _out325);
            _1532_recursiveGen = _out323;
            _1533___v100 = _out324;
            _1534_recIdents = _out325;
            r = ((_1532_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1534_recIdents;
            RAST._IExpr _out326;
            DCOMP._IOwnership _out327;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out326, out _out327);
            r = _out326;
            resultingOwnership = _out327;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1535_mapElems = _source71.dtor_mapElems;
          unmatched71 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1536_generatedValues;
            _1536_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1537_i;
            _1537_i = BigInteger.Zero;
            while ((_1537_i) < (new BigInteger((_1535_mapElems).Count))) {
              RAST._IExpr _1538_recursiveGenKey;
              DCOMP._IOwnership _1539___v101;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1540_recIdentsKey;
              RAST._IExpr _out328;
              DCOMP._IOwnership _out329;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out330;
              (this).GenExpr(((_1535_mapElems).Select(_1537_i)).dtor__0, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out328, out _out329, out _out330);
              _1538_recursiveGenKey = _out328;
              _1539___v101 = _out329;
              _1540_recIdentsKey = _out330;
              RAST._IExpr _1541_recursiveGenValue;
              DCOMP._IOwnership _1542___v102;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1543_recIdentsValue;
              RAST._IExpr _out331;
              DCOMP._IOwnership _out332;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out333;
              (this).GenExpr(((_1535_mapElems).Select(_1537_i)).dtor__1, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out331, out _out332, out _out333);
              _1541_recursiveGenValue = _out331;
              _1542___v102 = _out332;
              _1543_recIdentsValue = _out333;
              _1536_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1536_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1538_recursiveGenKey, _1541_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1540_recIdentsKey), _1543_recIdentsValue);
              _1537_i = (_1537_i) + (BigInteger.One);
            }
            _1537_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1544_arguments;
            _1544_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1537_i) < (new BigInteger((_1536_generatedValues).Count))) {
              RAST._IExpr _1545_genKey;
              _1545_genKey = ((_1536_generatedValues).Select(_1537_i)).dtor__0;
              RAST._IExpr _1546_genValue;
              _1546_genValue = ((_1536_generatedValues).Select(_1537_i)).dtor__1;
              _1544_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1544_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1545_genKey, _1546_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1537_i = (_1537_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _1544_arguments);
            RAST._IExpr _out334;
            DCOMP._IOwnership _out335;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out334, out _out335);
            r = _out334;
            resultingOwnership = _out335;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SeqUpdate) {
          DAST._IExpression _1547_expr = _source71.dtor_expr;
          DAST._IExpression _1548_index = _source71.dtor_indexExpr;
          DAST._IExpression _1549_value = _source71.dtor_value;
          unmatched71 = false;
          {
            RAST._IExpr _1550_exprR;
            DCOMP._IOwnership _1551___v103;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1552_exprIdents;
            RAST._IExpr _out336;
            DCOMP._IOwnership _out337;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out338;
            (this).GenExpr(_1547_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out336, out _out337, out _out338);
            _1550_exprR = _out336;
            _1551___v103 = _out337;
            _1552_exprIdents = _out338;
            RAST._IExpr _1553_indexR;
            DCOMP._IOwnership _1554_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1555_indexIdents;
            RAST._IExpr _out339;
            DCOMP._IOwnership _out340;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
            (this).GenExpr(_1548_index, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out339, out _out340, out _out341);
            _1553_indexR = _out339;
            _1554_indexOwnership = _out340;
            _1555_indexIdents = _out341;
            RAST._IExpr _1556_valueR;
            DCOMP._IOwnership _1557_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1558_valueIdents;
            RAST._IExpr _out342;
            DCOMP._IOwnership _out343;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out344;
            (this).GenExpr(_1549_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out342, out _out343, out _out344);
            _1556_valueR = _out342;
            _1557_valueOwnership = _out343;
            _1558_valueIdents = _out344;
            r = ((_1550_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_1553_indexR, _1556_valueR));
            RAST._IExpr _out345;
            DCOMP._IOwnership _out346;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out345, out _out346);
            r = _out345;
            resultingOwnership = _out346;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1552_exprIdents, _1555_indexIdents), _1558_valueIdents);
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MapUpdate) {
          DAST._IExpression _1559_expr = _source71.dtor_expr;
          DAST._IExpression _1560_index = _source71.dtor_indexExpr;
          DAST._IExpression _1561_value = _source71.dtor_value;
          unmatched71 = false;
          {
            RAST._IExpr _1562_exprR;
            DCOMP._IOwnership _1563___v104;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1564_exprIdents;
            RAST._IExpr _out347;
            DCOMP._IOwnership _out348;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
            (this).GenExpr(_1559_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out347, out _out348, out _out349);
            _1562_exprR = _out347;
            _1563___v104 = _out348;
            _1564_exprIdents = _out349;
            RAST._IExpr _1565_indexR;
            DCOMP._IOwnership _1566_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1567_indexIdents;
            RAST._IExpr _out350;
            DCOMP._IOwnership _out351;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
            (this).GenExpr(_1560_index, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out350, out _out351, out _out352);
            _1565_indexR = _out350;
            _1566_indexOwnership = _out351;
            _1567_indexIdents = _out352;
            RAST._IExpr _1568_valueR;
            DCOMP._IOwnership _1569_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1570_valueIdents;
            RAST._IExpr _out353;
            DCOMP._IOwnership _out354;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
            (this).GenExpr(_1561_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out353, out _out354, out _out355);
            _1568_valueR = _out353;
            _1569_valueOwnership = _out354;
            _1570_valueIdents = _out355;
            r = ((_1562_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(_1565_indexR, _1568_valueR));
            RAST._IExpr _out356;
            DCOMP._IOwnership _out357;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out356, out _out357);
            r = _out356;
            resultingOwnership = _out357;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1564_exprIdents, _1567_indexIdents), _1570_valueIdents);
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_This) {
          unmatched71 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source72 = selfIdent;
            bool unmatched72 = true;
            if (unmatched72) {
              if (_source72.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1571_id = _source72.dtor_value;
                unmatched72 = false;
                {
                  r = RAST.Expr.create_RawExpr(_1571_id);
                  if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                    r = RAST.__default.Clone(r);
                    resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
                  } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                    if (!(_1571_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.Borrow(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
                  } else {
                    if (!(_1571_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                      r = RAST.__default.BorrowMut(r);
                    }
                    resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
                  }
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1571_id);
                }
              }
            }
            if (unmatched72) {
              unmatched72 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out358;
                DCOMP._IOwnership _out359;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out358, out _out359);
                r = _out358;
                resultingOwnership = _out359;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Ite) {
          DAST._IExpression _1572_cond = _source71.dtor_cond;
          DAST._IExpression _1573_t = _source71.dtor_thn;
          DAST._IExpression _1574_f = _source71.dtor_els;
          unmatched71 = false;
          {
            RAST._IExpr _1575_cond;
            DCOMP._IOwnership _1576___v105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1577_recIdentsCond;
            RAST._IExpr _out360;
            DCOMP._IOwnership _out361;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out362;
            (this).GenExpr(_1572_cond, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out360, out _out361, out _out362);
            _1575_cond = _out360;
            _1576___v105 = _out361;
            _1577_recIdentsCond = _out362;
            Dafny.ISequence<Dafny.Rune> _1578_condString;
            _1578_condString = (_1575_cond)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1579___v106;
            DCOMP._IOwnership _1580_tHasToBeOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1581___v107;
            RAST._IExpr _out363;
            DCOMP._IOwnership _out364;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
            (this).GenExpr(_1573_t, selfIdent, @params, expectedOwnership, out _out363, out _out364, out _out365);
            _1579___v106 = _out363;
            _1580_tHasToBeOwned = _out364;
            _1581___v107 = _out365;
            RAST._IExpr _1582_fExpr;
            DCOMP._IOwnership _1583_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1584_recIdentsF;
            RAST._IExpr _out366;
            DCOMP._IOwnership _out367;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out368;
            (this).GenExpr(_1574_f, selfIdent, @params, _1580_tHasToBeOwned, out _out366, out _out367, out _out368);
            _1582_fExpr = _out366;
            _1583_fOwned = _out367;
            _1584_recIdentsF = _out368;
            Dafny.ISequence<Dafny.Rune> _1585_fString;
            _1585_fString = (_1582_fExpr)._ToString(DCOMP.__default.IND);
            RAST._IExpr _1586_tExpr;
            DCOMP._IOwnership _1587___v108;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1588_recIdentsT;
            RAST._IExpr _out369;
            DCOMP._IOwnership _out370;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
            (this).GenExpr(_1573_t, selfIdent, @params, _1583_fOwned, out _out369, out _out370, out _out371);
            _1586_tExpr = _out369;
            _1587___v108 = _out370;
            _1588_recIdentsT = _out371;
            Dafny.ISequence<Dafny.Rune> _1589_tString;
            _1589_tString = (_1586_tExpr)._ToString(DCOMP.__default.IND);
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1578_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1589_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1585_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
            RAST._IExpr _out372;
            DCOMP._IOwnership _out373;
            DCOMP.COMP.FromOwnership(r, _1583_fOwned, expectedOwnership, out _out372, out _out373);
            r = _out372;
            resultingOwnership = _out373;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1577_recIdentsCond, _1588_recIdentsT), _1584_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source71.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1590_e = _source71.dtor_expr;
            DAST.Format._IUnaryOpFormat _1591_format = _source71.dtor_format1;
            unmatched71 = false;
            {
              RAST._IExpr _1592_recursiveGen;
              DCOMP._IOwnership _1593___v109;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1594_recIdents;
              RAST._IExpr _out374;
              DCOMP._IOwnership _out375;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
              (this).GenExpr(_1590_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
              _1592_recursiveGen = _out374;
              _1593___v109 = _out375;
              _1594_recIdents = _out376;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1592_recursiveGen, _1591_format);
              RAST._IExpr _out377;
              DCOMP._IOwnership _out378;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out377, out _out378);
              r = _out377;
              resultingOwnership = _out378;
              readIdents = _1594_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source71.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1595_e = _source71.dtor_expr;
            DAST.Format._IUnaryOpFormat _1596_format = _source71.dtor_format1;
            unmatched71 = false;
            {
              RAST._IExpr _1597_recursiveGen;
              DCOMP._IOwnership _1598___v110;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1599_recIdents;
              RAST._IExpr _out379;
              DCOMP._IOwnership _out380;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out381;
              (this).GenExpr(_1595_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out379, out _out380, out _out381);
              _1597_recursiveGen = _out379;
              _1598___v110 = _out380;
              _1599_recIdents = _out381;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1597_recursiveGen, _1596_format);
              RAST._IExpr _out382;
              DCOMP._IOwnership _out383;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out382, out _out383);
              r = _out382;
              resultingOwnership = _out383;
              readIdents = _1599_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source71.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1600_e = _source71.dtor_expr;
            DAST.Format._IUnaryOpFormat _1601_format = _source71.dtor_format1;
            unmatched71 = false;
            {
              RAST._IExpr _1602_recursiveGen;
              DCOMP._IOwnership _1603_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1604_recIdents;
              RAST._IExpr _out384;
              DCOMP._IOwnership _out385;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out386;
              (this).GenExpr(_1600_e, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out384, out _out385, out _out386);
              _1602_recursiveGen = _out384;
              _1603_recOwned = _out385;
              _1604_recIdents = _out386;
              r = ((_1602_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out387;
              DCOMP._IOwnership _out388;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out387, out _out388);
              r = _out387;
              resultingOwnership = _out388;
              readIdents = _1604_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_BinOp) {
          DAST._IBinOp _1605___v111 = _source71.dtor_op;
          DAST._IExpression _1606___v112 = _source71.dtor_left;
          DAST._IExpression _1607___v113 = _source71.dtor_right;
          DAST.Format._IBinaryOpFormat _1608___v114 = _source71.dtor_format2;
          unmatched71 = false;
          RAST._IExpr _out389;
          DCOMP._IOwnership _out390;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
          (this).GenExprBinary(e, selfIdent, @params, expectedOwnership, out _out389, out _out390, out _out391);
          r = _out389;
          resultingOwnership = _out390;
          readIdents = _out391;
        }
      }
      if (unmatched71) {
        if (_source71.is_ArrayLen) {
          DAST._IExpression _1609_expr = _source71.dtor_expr;
          BigInteger _1610_dim = _source71.dtor_dim;
          unmatched71 = false;
          {
            RAST._IExpr _1611_recursiveGen;
            DCOMP._IOwnership _1612___v115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1613_recIdents;
            RAST._IExpr _out392;
            DCOMP._IOwnership _out393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out394;
            (this).GenExpr(_1609_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out392, out _out393, out _out394);
            _1611_recursiveGen = _out392;
            _1612___v115 = _out393;
            _1613_recIdents = _out394;
            if ((_1610_dim).Sign == 0) {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_1611_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
            } else {
              Dafny.ISequence<Dafny.Rune> _1614_s;
              _1614_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
              BigInteger _1615_i;
              _1615_i = BigInteger.One;
              while ((_1615_i) < (_1610_dim)) {
                _1614_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _1614_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
                _1615_i = (_1615_i) + (BigInteger.One);
              }
              r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1611_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _1614_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
            }
            RAST._IExpr _out395;
            DCOMP._IOwnership _out396;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out395, out _out396);
            r = _out395;
            resultingOwnership = _out396;
            readIdents = _1613_recIdents;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MapKeys) {
          DAST._IExpression _1616_expr = _source71.dtor_expr;
          unmatched71 = false;
          {
            RAST._IExpr _1617_recursiveGen;
            DCOMP._IOwnership _1618___v116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1619_recIdents;
            RAST._IExpr _out397;
            DCOMP._IOwnership _out398;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
            (this).GenExpr(_1616_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out397, out _out398, out _out399);
            _1617_recursiveGen = _out397;
            _1618___v116 = _out398;
            _1619_recIdents = _out399;
            readIdents = _1619_recIdents;
            r = RAST.Expr.create_Call((_1617_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out400;
            DCOMP._IOwnership _out401;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out400, out _out401);
            r = _out400;
            resultingOwnership = _out401;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MapValues) {
          DAST._IExpression _1620_expr = _source71.dtor_expr;
          unmatched71 = false;
          {
            RAST._IExpr _1621_recursiveGen;
            DCOMP._IOwnership _1622___v117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1623_recIdents;
            RAST._IExpr _out402;
            DCOMP._IOwnership _out403;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out404;
            (this).GenExpr(_1620_expr, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out402, out _out403, out _out404);
            _1621_recursiveGen = _out402;
            _1622___v117 = _out403;
            _1623_recIdents = _out404;
            readIdents = _1623_recIdents;
            r = RAST.Expr.create_Call((_1621_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out405;
            DCOMP._IOwnership _out406;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out405, out _out406);
            r = _out405;
            resultingOwnership = _out406;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SelectFn) {
          DAST._IExpression _1624_on = _source71.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1625_field = _source71.dtor_field;
          bool _1626_isDatatype = _source71.dtor_onDatatype;
          bool _1627_isStatic = _source71.dtor_isStatic;
          BigInteger _1628_arity = _source71.dtor_arity;
          unmatched71 = false;
          {
            RAST._IExpr _1629_onExpr;
            DCOMP._IOwnership _1630_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1631_recIdents;
            RAST._IExpr _out407;
            DCOMP._IOwnership _out408;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
            (this).GenExpr(_1624_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out407, out _out408, out _out409);
            _1629_onExpr = _out407;
            _1630_onOwned = _out408;
            _1631_recIdents = _out409;
            Dafny.ISequence<Dafny.Rune> _1632_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1633_onString;
            _1633_onString = (_1629_onExpr)._ToString(DCOMP.__default.IND);
            if (_1627_isStatic) {
              _1632_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1633_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_1625_field));
            } else {
              _1632_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1632_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1632_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1633_onString), ((object.Equals(_1630_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1634_args;
              _1634_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1635_i;
              _1635_i = BigInteger.Zero;
              while ((_1635_i) < (_1628_arity)) {
                if ((_1635_i).Sign == 1) {
                  _1634_args = Dafny.Sequence<Dafny.Rune>.Concat(_1634_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1634_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1634_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1635_i));
                _1635_i = (_1635_i) + (BigInteger.One);
              }
              _1632_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1632_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1634_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1632_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1632_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _1625_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1634_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1632_s = Dafny.Sequence<Dafny.Rune>.Concat(_1632_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1632_s = Dafny.Sequence<Dafny.Rune>.Concat(_1632_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1636_typeShape;
            _1636_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1637_i;
            _1637_i = BigInteger.Zero;
            while ((_1637_i) < (_1628_arity)) {
              if ((_1637_i).Sign == 1) {
                _1636_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1636_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1636_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1636_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1637_i = (_1637_i) + (BigInteger.One);
            }
            _1636_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1636_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1632_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper(::std::rc::Rc::new("), _1632_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1636_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">)"));
            r = RAST.Expr.create_RawExpr(_1632_s);
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out410, out _out411);
            r = _out410;
            resultingOwnership = _out411;
            readIdents = _1631_recIdents;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Select) {
          DAST._IExpression expr0 = _source71.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1638_c = expr0.dtor_Companion_i_a0;
            Dafny.ISequence<Dafny.Rune> _1639_field = _source71.dtor_field;
            bool _1640_isConstant = _source71.dtor_isConstant;
            bool _1641_isDatatype = _source71.dtor_onDatatype;
            unmatched71 = false;
            {
              RAST._IExpr _1642_onExpr;
              DCOMP._IOwnership _1643_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1644_recIdents;
              RAST._IExpr _out412;
              DCOMP._IOwnership _out413;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
              (this).GenExpr(DAST.Expression.create_Companion(_1638_c), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out412, out _out413, out _out414);
              _1642_onExpr = _out412;
              _1643_onOwned = _out413;
              _1644_recIdents = _out414;
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1642_onExpr)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_1639_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")));
              RAST._IExpr _out415;
              DCOMP._IOwnership _out416;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out415, out _out416);
              r = _out415;
              resultingOwnership = _out416;
              readIdents = _1644_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Select) {
          DAST._IExpression _1645_on = _source71.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1646_field = _source71.dtor_field;
          bool _1647_isConstant = _source71.dtor_isConstant;
          bool _1648_isDatatype = _source71.dtor_onDatatype;
          unmatched71 = false;
          {
            RAST._IExpr _1649_onExpr;
            DCOMP._IOwnership _1650_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1651_recIdents;
            RAST._IExpr _out417;
            DCOMP._IOwnership _out418;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
            (this).GenExpr(_1645_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out417, out _out418, out _out419);
            _1649_onExpr = _out417;
            _1650_onOwned = _out418;
            _1651_recIdents = _out419;
            if ((_1648_isDatatype) || (_1647_isConstant)) {
              r = RAST.Expr.create_Call((_1649_onExpr).Sel(DCOMP.__default.escapeIdent(_1646_field)), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out420;
              DCOMP._IOwnership _out421;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out420, out _out421);
              r = _out420;
              resultingOwnership = _out421;
            } else {
              Dafny.ISequence<Dafny.Rune> _1652_s = Dafny.Sequence<Dafny.Rune>.Empty;
              _1652_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_1649_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeIdent(_1646_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              RAST._IExpr _out422;
              DCOMP._IOwnership _out423;
              DCOMP.COMP.FromOwnership(RAST.Expr.create_RawExpr(_1652_s), DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out422, out _out423);
              r = _out422;
              resultingOwnership = _out423;
            }
            readIdents = _1651_recIdents;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Index) {
          DAST._IExpression _1653_on = _source71.dtor_expr;
          DAST._ICollKind _1654_collKind = _source71.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _1655_indices = _source71.dtor_indices;
          unmatched71 = false;
          {
            RAST._IExpr _1656_onExpr;
            DCOMP._IOwnership _1657_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1658_recIdents;
            RAST._IExpr _out424;
            DCOMP._IOwnership _out425;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out426;
            (this).GenExpr(_1653_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out424, out _out425, out _out426);
            _1656_onExpr = _out424;
            _1657_onOwned = _out425;
            _1658_recIdents = _out426;
            readIdents = _1658_recIdents;
            r = _1656_onExpr;
            BigInteger _1659_i;
            _1659_i = BigInteger.Zero;
            while ((_1659_i) < (new BigInteger((_1655_indices).Count))) {
              if (object.Equals(_1654_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _1660_idx;
              DCOMP._IOwnership _1661_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1662_recIdentsIdx;
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExpr((_1655_indices).Select(_1659_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out427, out _out428, out _out429);
              _1660_idx = _out427;
              _1661_idxOwned = _out428;
              _1662_recIdentsIdx = _out429;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1660_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1662_recIdentsIdx);
              _1659_i = (_1659_i) + (BigInteger.One);
            }
            RAST._IExpr _out430;
            DCOMP._IOwnership _out431;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out430, out _out431);
            r = _out430;
            resultingOwnership = _out431;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_IndexRange) {
          DAST._IExpression _1663_on = _source71.dtor_expr;
          bool _1664_isArray = _source71.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _1665_low = _source71.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _1666_high = _source71.dtor_high;
          unmatched71 = false;
          {
            RAST._IExpr _1667_onExpr;
            DCOMP._IOwnership _1668_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1669_recIdents;
            RAST._IExpr _out432;
            DCOMP._IOwnership _out433;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out434;
            (this).GenExpr(_1663_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out432, out _out433, out _out434);
            _1667_onExpr = _out432;
            _1668_onOwned = _out433;
            _1669_recIdents = _out434;
            readIdents = _1669_recIdents;
            Dafny.ISequence<Dafny.Rune> _1670_methodName;
            _1670_methodName = (((_1665_low).is_Some) ? ((((_1666_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_1666_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _1671_arguments;
            _1671_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source73 = _1665_low;
            bool unmatched73 = true;
            if (unmatched73) {
              if (_source73.is_Some) {
                DAST._IExpression _1672_l = _source73.dtor_value;
                unmatched73 = false;
                {
                  RAST._IExpr _1673_lExpr;
                  DCOMP._IOwnership _1674___v118;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1675_recIdentsL;
                  RAST._IExpr _out435;
                  DCOMP._IOwnership _out436;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
                  (this).GenExpr(_1672_l, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out435, out _out436, out _out437);
                  _1673_lExpr = _out435;
                  _1674___v118 = _out436;
                  _1675_recIdentsL = _out437;
                  _1671_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1671_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1673_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1675_recIdentsL);
                }
              }
            }
            if (unmatched73) {
              unmatched73 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source74 = _1666_high;
            bool unmatched74 = true;
            if (unmatched74) {
              if (_source74.is_Some) {
                DAST._IExpression _1676_h = _source74.dtor_value;
                unmatched74 = false;
                {
                  RAST._IExpr _1677_hExpr;
                  DCOMP._IOwnership _1678___v119;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1679_recIdentsH;
                  RAST._IExpr _out438;
                  DCOMP._IOwnership _out439;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
                  (this).GenExpr(_1676_h, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out438, out _out439, out _out440);
                  _1677_hExpr = _out438;
                  _1678___v119 = _out439;
                  _1679_recIdentsH = _out440;
                  _1671_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1671_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1677_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1679_recIdentsH);
                }
              }
            }
            if (unmatched74) {
              unmatched74 = false;
            }
            r = _1667_onExpr;
            if (_1664_isArray) {
              if (!(_1670_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _1670_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1670_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _1670_methodName))).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _1671_arguments);
            } else {
              if (!(_1670_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_1670_methodName)).Apply(Dafny.Sequence<RAST._IType>.FromElements(), _1671_arguments);
              }
            }
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out441, out _out442);
            r = _out441;
            resultingOwnership = _out442;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_TupleSelect) {
          DAST._IExpression _1680_on = _source71.dtor_expr;
          BigInteger _1681_idx = _source71.dtor_index;
          unmatched71 = false;
          {
            RAST._IExpr _1682_onExpr;
            DCOMP._IOwnership _1683_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1684_recIdents;
            RAST._IExpr _out443;
            DCOMP._IOwnership _out444;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
            (this).GenExpr(_1680_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out443, out _out444, out _out445);
            _1682_onExpr = _out443;
            _1683_onOwnership = _out444;
            _1684_recIdents = _out445;
            r = (_1682_onExpr).Sel(Std.Strings.__default.OfNat(_1681_idx));
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            DCOMP.COMP.FromOwnership(r, _1683_onOwnership, expectedOwnership, out _out446, out _out447);
            r = _out446;
            resultingOwnership = _out447;
            readIdents = _1684_recIdents;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Call) {
          DAST._IExpression _1685_on = _source71.dtor_on;
          DAST._ICallName _1686_name = _source71.dtor_callName;
          Dafny.ISequence<DAST._IType> _1687_typeArgs = _source71.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1688_args = _source71.dtor_args;
          unmatched71 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IType> _1689_typeExprs;
            _1689_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            if ((new BigInteger((_1687_typeArgs).Count)) >= (BigInteger.One)) {
              BigInteger _1690_typeI;
              _1690_typeI = BigInteger.Zero;
              while ((_1690_typeI) < (new BigInteger((_1687_typeArgs).Count))) {
                RAST._IType _1691_typeExpr;
                RAST._IType _out448;
                _out448 = (this).GenType((_1687_typeArgs).Select(_1690_typeI), false, false);
                _1691_typeExpr = _out448;
                _1689_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1689_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1691_typeExpr));
                _1690_typeI = (_1690_typeI) + (BigInteger.One);
              }
            }
            Dafny.ISequence<RAST._IExpr> _1692_argExprs;
            _1692_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _1693_i;
            _1693_i = BigInteger.Zero;
            while ((_1693_i) < (new BigInteger((_1688_args).Count))) {
              RAST._IExpr _1694_argExpr;
              DCOMP._IOwnership _1695_argOwnership;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1696_argIdents;
              RAST._IExpr _out449;
              DCOMP._IOwnership _out450;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
              (this).GenExpr((_1688_args).Select(_1693_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out449, out _out450, out _out451);
              _1694_argExpr = _out449;
              _1695_argOwnership = _out450;
              _1696_argIdents = _out451;
              _1692_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1692_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1694_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1696_argIdents);
              _1693_i = (_1693_i) + (BigInteger.One);
            }
            RAST._IExpr _1697_onExpr;
            DCOMP._IOwnership _1698___v120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1699_recIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_1685_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out452, out _out453, out _out454);
            _1697_onExpr = _out452;
            _1698___v120 = _out453;
            _1699_recIdents = _out454;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1699_recIdents);
            Dafny.ISequence<Dafny.Rune> _1700_renderedName;
            _1700_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
              DAST._ICallName _source75 = _1686_name;
              bool unmatched75 = true;
              if (unmatched75) {
                if (_source75.is_Name) {
                  Dafny.ISequence<Dafny.Rune> _1701_ident = _source75.dtor_name;
                  unmatched75 = false;
                  return DCOMP.__default.escapeIdent(_1701_ident);
                }
              }
              if (unmatched75) {
                bool disjunctiveMatch12 = false;
                if (_source75.is_MapBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (_source75.is_SetBuilderAdd) {
                  disjunctiveMatch12 = true;
                }
                if (disjunctiveMatch12) {
                  unmatched75 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                }
              }
              if (unmatched75) {
                bool disjunctiveMatch13 = false;
                disjunctiveMatch13 = true;
                disjunctiveMatch13 = true;
                if (disjunctiveMatch13) {
                  unmatched75 = false;
                  return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                }
              }
              throw new System.Exception("unexpected control point");
            }))();
            DAST._IExpression _source76 = _1685_on;
            bool unmatched76 = true;
            if (unmatched76) {
              if (_source76.is_Companion) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1702___v121 = _source76.dtor_Companion_i_a0;
                unmatched76 = false;
                {
                  _1697_onExpr = (_1697_onExpr).MSel(_1700_renderedName);
                }
              }
            }
            if (unmatched76) {
              DAST._IExpression _1703___v122 = _source76;
              unmatched76 = false;
              {
                _1697_onExpr = (_1697_onExpr).Sel(_1700_renderedName);
              }
            }
            r = RAST.Expr.create_Call(_1697_onExpr, _1689_typeExprs, _1692_argExprs);
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out455, out _out456);
            r = _out455;
            resultingOwnership = _out456;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _1704_params = _source71.dtor_params;
          DAST._IType _1705_retType = _source71.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _1706_body = _source71.dtor_body;
          unmatched71 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1707_paramNames;
            _1707_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1708_i;
            _1708_i = BigInteger.Zero;
            while ((_1708_i) < (new BigInteger((_1704_params).Count))) {
              _1707_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1707_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_1704_params).Select(_1708_i)).dtor_name));
              _1708_i = (_1708_i) + (BigInteger.One);
            }
            RAST._IExpr _1709_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1710_recIdents;
            RAST._IExpr _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenStmts(_1706_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _1707_paramNames, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out457, out _out458);
            _1709_recursiveGen = _out457;
            _1710_recIdents = _out458;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<Dafny.Rune> _1711_allReadCloned;
            _1711_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            while (!(_1710_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _1712_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_1710_recIdents).Elements) {
                _1712_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_1710_recIdents).Contains(_1712_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 3278)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_1712_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                  _1711_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(_1711_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let _this = self.clone();\n"));
                }
              } else if (!((_1707_paramNames).Contains(_1712_next))) {
                _1711_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1711_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent(_1712_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), DCOMP.__default.escapeIdent(_1712_next)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1712_next));
              }
              _1710_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1710_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1712_next));
            }
            Dafny.ISequence<Dafny.Rune> _1713_paramsString;
            _1713_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            Dafny.ISequence<Dafny.Rune> _1714_paramTypes;
            _1714_paramTypes = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            _1708_i = BigInteger.Zero;
            while ((_1708_i) < (new BigInteger((_1704_params).Count))) {
              if ((_1708_i).Sign == 1) {
                _1713_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_1713_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _1714_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_1714_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              RAST._IType _1715_typStr;
              RAST._IType _out459;
              _out459 = (this).GenType(((_1704_params).Select(_1708_i)).dtor_typ, false, true);
              _1715_typStr = _out459;
              _1713_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1713_paramsString, DCOMP.__default.escapeIdent(((_1704_params).Select(_1708_i)).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (RAST.Type.create_Borrowed(_1715_typStr))._ToString(DCOMP.__default.IND));
              _1714_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_1714_paramTypes, (RAST.Type.create_Borrowed(_1715_typStr))._ToString(DCOMP.__default.IND));
              _1708_i = (_1708_i) + (BigInteger.One);
            }
            RAST._IType _1716_retTypeGen;
            RAST._IType _out460;
            _out460 = (this).GenType(_1705_retType, false, true);
            _1716_retTypeGen = _out460;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn("), _1714_paramTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), (_1716_retTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>({\n")), _1711_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(move |")), _1713_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), (_1716_retTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), (_1709_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})")));
            RAST._IExpr _out461;
            DCOMP._IOwnership _out462;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out461, out _out462);
            r = _out461;
            resultingOwnership = _out462;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _1717_values = _source71.dtor_values;
          DAST._IType _1718_retType = _source71.dtor_retType;
          DAST._IExpression _1719_expr = _source71.dtor_expr;
          unmatched71 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1720_paramNames;
            _1720_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1721_paramNamesSet;
            _1721_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1722_i;
            _1722_i = BigInteger.Zero;
            while ((_1722_i) < (new BigInteger((_1717_values).Count))) {
              _1720_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1720_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((_1717_values).Select(_1722_i)).dtor__0).dtor_name));
              _1721_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1721_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((((_1717_values).Select(_1722_i)).dtor__0).dtor_name));
              _1722_i = (_1722_i) + (BigInteger.One);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<Dafny.Rune> _1723_s;
            _1723_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            Dafny.ISequence<Dafny.Rune> _1724_paramsString;
            _1724_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            _1722_i = BigInteger.Zero;
            while ((_1722_i) < (new BigInteger((_1717_values).Count))) {
              if ((_1722_i).Sign == 1) {
                _1724_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_1724_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              RAST._IType _1725_typStr;
              RAST._IType _out463;
              _out463 = (this).GenType((((_1717_values).Select(_1722_i)).dtor__0).dtor_typ, false, true);
              _1725_typStr = _out463;
              RAST._IExpr _1726_valueGen;
              DCOMP._IOwnership _1727___v123;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1728_recIdents;
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExpr(((_1717_values).Select(_1722_i)).dtor__1, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out464, out _out465, out _out466);
              _1726_valueGen = _out464;
              _1727___v123 = _out465;
              _1728_recIdents = _out466;
              _1723_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1723_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), DCOMP.__default.escapeIdent((((_1717_values).Select(_1722_i)).dtor__0).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_1725_typStr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1728_recIdents);
              _1723_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1723_s, (_1726_valueGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              _1722_i = (_1722_i) + (BigInteger.One);
            }
            RAST._IExpr _1729_recGen;
            DCOMP._IOwnership _1730_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1731_recIdents;
            RAST._IExpr _out467;
            DCOMP._IOwnership _out468;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out469;
            (this).GenExpr(_1719_expr, selfIdent, _1720_paramNames, expectedOwnership, out _out467, out _out468, out _out469);
            _1729_recGen = _out467;
            _1730_recOwned = _out468;
            _1731_recIdents = _out469;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1731_recIdents, _1721_paramNamesSet);
            _1723_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1723_s, (_1729_recGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
            r = RAST.Expr.create_RawExpr(_1723_s);
            RAST._IExpr _out470;
            DCOMP._IOwnership _out471;
            DCOMP.COMP.FromOwnership(r, _1730_recOwned, expectedOwnership, out _out470, out _out471);
            r = _out470;
            resultingOwnership = _out471;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _1732_name = _source71.dtor_name;
          DAST._IType _1733_tpe = _source71.dtor_typ;
          DAST._IExpression _1734_value = _source71.dtor_value;
          DAST._IExpression _1735_iifeBody = _source71.dtor_iifeBody;
          unmatched71 = false;
          {
            RAST._IExpr _1736_valueGen;
            DCOMP._IOwnership _1737___v124;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1738_recIdents;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_1734_value, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out472, out _out473, out _out474);
            _1736_valueGen = _out472;
            _1737___v124 = _out473;
            _1738_recIdents = _out474;
            readIdents = _1738_recIdents;
            RAST._IType _1739_valueTypeGen;
            RAST._IType _out475;
            _out475 = (this).GenType(_1733_tpe, false, true);
            _1739_valueTypeGen = _out475;
            RAST._IExpr _1740_bodyGen;
            DCOMP._IOwnership _1741___v125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1742_bodyIdents;
            RAST._IExpr _out476;
            DCOMP._IOwnership _out477;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out478;
            (this).GenExpr(_1735_iifeBody, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out476, out _out477, out _out478);
            _1740_bodyGen = _out476;
            _1741___v125 = _out477;
            _1742_bodyIdents = _out478;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1742_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1732_name))));
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet "), DCOMP.__default.escapeIdent((_1732_name))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_1739_valueTypeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (_1736_valueGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), (_1740_bodyGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")));
            RAST._IExpr _out479;
            DCOMP._IOwnership _out480;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out479, out _out480);
            r = _out479;
            resultingOwnership = _out480;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_Apply) {
          DAST._IExpression _1743_func = _source71.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _1744_args = _source71.dtor_args;
          unmatched71 = false;
          {
            RAST._IExpr _1745_funcExpr;
            DCOMP._IOwnership _1746___v126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_recIdents;
            RAST._IExpr _out481;
            DCOMP._IOwnership _out482;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out483;
            (this).GenExpr(_1743_func, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out481, out _out482, out _out483);
            _1745_funcExpr = _out481;
            _1746___v126 = _out482;
            _1747_recIdents = _out483;
            readIdents = _1747_recIdents;
            Dafny.ISequence<Dafny.Rune> _1748_argString;
            _1748_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _1749_i;
            _1749_i = BigInteger.Zero;
            while ((_1749_i) < (new BigInteger((_1744_args).Count))) {
              if ((_1749_i).Sign == 1) {
                _1748_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1748_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              RAST._IExpr _1750_argExpr;
              DCOMP._IOwnership _1751_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1752_argIdents;
              RAST._IExpr _out484;
              DCOMP._IOwnership _out485;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out486;
              (this).GenExpr((_1744_args).Select(_1749_i), selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out484, out _out485, out _out486);
              _1750_argExpr = _out484;
              _1751_argOwned = _out485;
              _1752_argIdents = _out486;
              Dafny.ISequence<Dafny.Rune> _1753_argExprString;
              _1753_argExprString = (_1750_argExpr)._ToString(DCOMP.__default.IND);
              if (object.Equals(_1751_argOwned, DCOMP.Ownership.create_OwnershipOwned())) {
                _1753_argExprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _1753_argExprString);
              }
              _1748_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1748_argString, _1753_argExprString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1752_argIdents);
              _1749_i = (_1749_i) + (BigInteger.One);
            }
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1745_funcExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1748_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))")));
            RAST._IExpr _out487;
            DCOMP._IOwnership _out488;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out487, out _out488);
            r = _out487;
            resultingOwnership = _out488;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_TypeTest) {
          DAST._IExpression _1754_on = _source71.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1755_dType = _source71.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _1756_variant = _source71.dtor_variant;
          unmatched71 = false;
          {
            RAST._IExpr _1757_exprGen;
            DCOMP._IOwnership _1758___v127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1759_recIdents;
            RAST._IExpr _out489;
            DCOMP._IOwnership _out490;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out491;
            (this).GenExpr(_1754_on, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out489, out _out490, out _out491);
            _1757_exprGen = _out489;
            _1758___v127 = _out490;
            _1759_recIdents = _out491;
            Dafny.ISequence<Dafny.Rune> _1760_dTypePath;
            Dafny.ISequence<Dafny.Rune> _out492;
            _out492 = DCOMP.COMP.GenPath(_1755_dType);
            _1760_dTypePath = _out492;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), (_1757_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _1760_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeIdent(_1756_variant)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })")));
            RAST._IExpr _out493;
            DCOMP._IOwnership _out494;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out493, out _out494);
            r = _out493;
            resultingOwnership = _out494;
            readIdents = _1759_recIdents;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_BoolBoundedPool) {
          unmatched71 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out495, out _out496);
            r = _out495;
            resultingOwnership = _out496;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SetBoundedPool) {
          DAST._IExpression _1761_of = _source71.dtor_of;
          unmatched71 = false;
          {
            RAST._IExpr _1762_exprGen;
            DCOMP._IOwnership _1763___v128;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1764_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_1761_of, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out497, out _out498, out _out499);
            _1762_exprGen = _out497;
            _1763___v128 = _out498;
            _1764_recIdents = _out499;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1762_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").iter()")));
            RAST._IExpr _out500;
            DCOMP._IOwnership _out501;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out500, out _out501);
            r = _out500;
            resultingOwnership = _out501;
            readIdents = _1764_recIdents;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_SeqBoundedPool) {
          DAST._IExpression _1765_of = _source71.dtor_of;
          bool _1766_includeDuplicates = _source71.dtor_includeDuplicates;
          unmatched71 = false;
          {
            RAST._IExpr _1767_exprGen;
            DCOMP._IOwnership _1768___v129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1769_recIdents;
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
            (this).GenExpr(_1765_of, selfIdent, @params, DCOMP.Ownership.create_OwnershipBorrowed(), out _out502, out _out503, out _out504);
            _1767_exprGen = _out502;
            _1768___v129 = _out503;
            _1769_recIdents = _out504;
            Dafny.ISequence<Dafny.Rune> _1770_s;
            _1770_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_1767_exprGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").iter()"));
            if (!(_1766_includeDuplicates)) {
              _1770_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::itertools::Itertools::unique("), _1770_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            r = RAST.Expr.create_RawExpr(_1770_s);
            RAST._IExpr _out505;
            DCOMP._IOwnership _out506;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out505, out _out506);
            r = _out505;
            resultingOwnership = _out506;
            readIdents = _1769_recIdents;
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_IntRange) {
          DAST._IExpression _1771_lo = _source71.dtor_lo;
          DAST._IExpression _1772_hi = _source71.dtor_hi;
          unmatched71 = false;
          {
            RAST._IExpr _1773_lo;
            DCOMP._IOwnership _1774___v130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1775_recIdentsLo;
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
            (this).GenExpr(_1771_lo, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out507, out _out508, out _out509);
            _1773_lo = _out507;
            _1774___v130 = _out508;
            _1775_recIdentsLo = _out509;
            RAST._IExpr _1776_hi;
            DCOMP._IOwnership _1777___v131;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1778_recIdentsHi;
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out512;
            (this).GenExpr(_1772_hi, selfIdent, @params, DCOMP.Ownership.create_OwnershipOwned(), out _out510, out _out511, out _out512);
            _1776_hi = _out510;
            _1777___v131 = _out511;
            _1778_recIdentsHi = _out512;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::integer_range("), (_1773_lo)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), (_1776_hi)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
            RAST._IExpr _out513;
            DCOMP._IOwnership _out514;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out513, out _out514);
            r = _out513;
            resultingOwnership = _out514;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1775_recIdentsLo, _1778_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched71) {
        if (_source71.is_MapBuilder) {
          DAST._IType _1779_keyType = _source71.dtor_keyType;
          DAST._IType _1780_valueType = _source71.dtor_valueType;
          unmatched71 = false;
          {
            RAST._IType _1781_kType;
            RAST._IType _out515;
            _out515 = (this).GenType(_1779_keyType, false, false);
            _1781_kType = _out515;
            RAST._IType _1782_vType;
            RAST._IType _out516;
            _out516 = (this).GenType(_1780_valueType, false, false);
            _1782_vType = _out516;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::MapBuilder::<"), (_1781_kType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), (_1782_vType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::new()")));
            RAST._IExpr _out517;
            DCOMP._IOwnership _out518;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out517, out _out518);
            r = _out517;
            resultingOwnership = _out518;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched71) {
        DAST._IType _1783_elemType = _source71.dtor_elemType;
        unmatched71 = false;
        {
          RAST._IType _1784_eType;
          RAST._IType _out519;
          _out519 = (this).GenType(_1783_elemType, false, false);
          _1784_eType = _out519;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::SetBuilder::<"), (_1784_eType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">::new()")));
          RAST._IExpr _out520;
          DCOMP._IOwnership _out521;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out520, out _out521);
          r = _out520;
          resultingOwnership = _out521;
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
      BigInteger _1785_i;
      _1785_i = BigInteger.Zero;
      while ((_1785_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _1786_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _1787_m;
        RAST._IMod _out522;
        _out522 = (this).GenModule((p).Select(_1785_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _1787_m = _out522;
        _1786_generated = (_1787_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_1785_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1786_generated);
        _1785_i = (_1785_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _1788_i;
      _1788_i = BigInteger.Zero;
      while ((_1788_i) < (new BigInteger((fullName).Count))) {
        if ((_1788_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeIdent((fullName).Select(_1788_i)));
        _1788_i = (_1788_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
    public bool _i_UnicodeChars {get; set;}
    public bool UnicodeChars { get {
      return this._i_UnicodeChars;
    } }
    public Dafny.ISequence<Dafny.Rune> DafnyChar { get {
      if ((this).UnicodeChars) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyChar");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyCharUTF16");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> string__of { get {
      if ((this).UnicodeChars) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_of");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_utf16_of");
      }
    } }
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
  }
} // end of namespace DCOMP