// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace RAST {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> SeqToString<__T>(Dafny.ISequence<__T> s, Func<__T, Dafny.ISequence<Dafny.Rune>> f, Dafny.ISequence<Dafny.Rune> separator)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Helpers.Id<Func<__T, Dafny.ISequence<Dafny.Rune>>>(f)((s).Select(BigInteger.Zero)), (((new BigInteger((s).Count)) > (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.Concat(separator, RAST.__default.SeqToString<__T>((s).Drop(BigInteger.One), f, separator))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
      }
    }
    public static BigInteger SeqToHeight<__T>(Dafny.ISequence<__T> s, Func<__T, BigInteger> f)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        BigInteger _763_i = Dafny.Helpers.Id<Func<__T, BigInteger>>(f)((s).Select(BigInteger.Zero));
        BigInteger _764_j = RAST.__default.SeqToHeight<__T>((s).Drop(BigInteger.One), f);
        if ((_763_i) < (_764_j)) {
          return _764_j;
        } else {
          return _763_i;
        }
      }
    }
    public static RAST._IType Rc(RAST._IType underlying) {
      return RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Rc")), Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IType RefCell(RAST._IType underlying) {
      return RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cell"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("RefCell")), Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IType Vec(RAST._IType underlying) {
      return RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Vec")), Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IExpr NewVec(Dafny.ISequence<RAST._IExpr> elements) {
      return RAST.Expr.create_Call(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec!")), Dafny.Sequence<RAST._IType>.FromElements(), elements);
    }
    public static RAST._IExpr Clone(RAST._IExpr underlying) {
      return RAST.Expr.create_Call(RAST.Expr.create_Select(underlying, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone")), Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements());
    }
    public static RAST._IExpr Borrow(RAST._IExpr underlying) {
      return RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), underlying, DAST.Format.UnaryOpFormat.create_NoFormat());
    }
    public static RAST._IExpr BorrowMut(RAST._IExpr underlying) {
      return RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"), underlying, DAST.Format.UnaryOpFormat.create_NoFormat());
    }
    public static RAST._IType RawType(Dafny.ISequence<Dafny.Rune> content) {
      return RAST.Type.create_TIdentifier(content);
    }
    public static Dafny.ISequence<Dafny.Rune> AddIndent(Dafny.ISequence<Dafny.Rune> raw, Dafny.ISequence<Dafny.Rune> ind)
    {
      Dafny.ISequence<Dafny.Rune> _765___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((raw).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_765___accumulator, raw);
      } else if ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[({")).Contains((raw).Select(BigInteger.Zero))) {
        _765___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_765___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in103 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in104 = Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND);
        raw = _in103;
        ind = _in104;
        goto TAIL_CALL_START;
      } else if (((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("})]")).Contains((raw).Select(BigInteger.Zero))) && ((new BigInteger((ind).Count)) > (new BigInteger(2)))) {
        _765___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_765___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in105 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in106 = (ind).Take((new BigInteger((ind).Count)) - (new BigInteger(2)));
        raw = _in105;
        ind = _in106;
        goto TAIL_CALL_START;
      } else if (((raw).Select(BigInteger.Zero)) == (new Dafny.Rune('\n'))) {
        _765___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_765___accumulator, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)), ind));
        Dafny.ISequence<Dafny.Rune> _in107 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in108 = ind;
        raw = _in107;
        ind = _in108;
        goto TAIL_CALL_START;
      } else {
        _765___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_765___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in109 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in110 = ind;
        raw = _in109;
        ind = _in110;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger max(BigInteger i, BigInteger j)
    {
      if ((i) < (j)) {
        return j;
      } else {
        return i;
      }
    }
    public static RAST._IExpr RcNew(RAST._IExpr underlying) {
      return RAST.Expr.create_Call(RAST.__default.std__rc__Rc__new, Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(underlying));
    }
    public static RAST._IType Self { get {
      return RAST.Type.create_Borrowed(RAST.Type.create_SelfOwned());
    } }
    public static RAST._IType SelfMut { get {
      return RAST.Type.create_BorrowedMut(RAST.Type.create_SelfOwned());
    } }
    public static RAST._IType global__type { get {
      return RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
    } }
    public static RAST._IType std__type { get {
      return (RAST.__default.global__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"));
    } }
    public static RAST._IType CloneTrait { get {
      return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Clone"));
    } }
    public static RAST._IType DafnyPrintTrait { get {
      return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint"));
    } }
    public static RAST._IType DefaultTrait { get {
      return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default"));
    } }
    public static RAST._IType StaticTrait { get {
      return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'static"));
    } }
    public static RAST._IType cell__type { get {
      return (RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cell"));
    } }
    public static RAST._IType refcell__type { get {
      return (RAST.__default.cell__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("RefCell"));
    } }
    public static RAST._IType dafny__runtime__type { get {
      return (RAST.__default.global__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime"));
    } }
    public static Dafny.ISequence<Dafny.Rune> IND { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  ");
    } }
    public static RAST._IExpr @global { get {
      return RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
    } }
    public static RAST._IExpr dafny__runtime { get {
      return (RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime"));
    } }
    public static RAST._IExpr dafny__runtime__Set { get {
      return (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"));
    } }
    public static RAST._IExpr dafny__runtime__Set__from__array { get {
      return (RAST.__default.dafny__runtime__Set).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"));
    } }
    public static RAST._IExpr dafny__runtime__Sequence { get {
      return (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"));
    } }
    public static RAST._IExpr Sequence__from__array__owned { get {
      return (RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array_owned"));
    } }
    public static RAST._IExpr Sequence__from__array { get {
      return (RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"));
    } }
    public static RAST._IExpr dafny__runtime__Multiset { get {
      return (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"));
    } }
    public static RAST._IExpr dafny__runtime__Multiset__from__array { get {
      return (RAST.__default.dafny__runtime__Multiset).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"));
    } }
    public static RAST._IExpr std { get {
      return (RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"));
    } }
    public static RAST._IExpr std__rc { get {
      return (RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc"));
    } }
    public static RAST._IExpr std__rc__Rc { get {
      return (RAST.__default.std__rc).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Rc"));
    } }
    public static RAST._IExpr std__rc__Rc__new { get {
      return (RAST.__default.std__rc__Rc).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"));
    } }
  }

  public interface _IMod {
    bool is_Mod { get; }
    bool is_ExternMod { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._IModDecl> dtor_body { get; }
    _IMod DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public abstract class Mod : _IMod {
    public Mod() {
    }
    private static readonly RAST._IMod theDefault = create_Mod(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IModDecl>.Empty);
    public static RAST._IMod Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IMod> _TYPE = new Dafny.TypeDescriptor<RAST._IMod>(RAST.Mod.Default());
    public static Dafny.TypeDescriptor<RAST._IMod> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMod create_Mod(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IModDecl> body) {
      return new Mod_Mod(name, body);
    }
    public static _IMod create_ExternMod(Dafny.ISequence<Dafny.Rune> name) {
      return new Mod_ExternMod(name);
    }
    public bool is_Mod { get { return this is Mod_Mod; } }
    public bool is_ExternMod { get { return this is Mod_ExternMod; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Mod_Mod) { return ((Mod_Mod)d)._i_name; }
        return ((Mod_ExternMod)d)._i_name;
      }
    }
    public Dafny.ISequence<RAST._IModDecl> dtor_body {
      get {
        var d = this;
        return ((Mod_Mod)d)._i_body;
      }
    }
    public abstract _IMod DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      var _pat_let_tv23 = ind;
      var _pat_let_tv24 = ind;
      var _pat_let_tv25 = ind;
      var _pat_let_tv26 = ind;
      RAST._IMod _source25 = this;
      bool unmatched25 = true;
      if (unmatched25) {
        if (_source25.is_ExternMod) {
          Dafny.ISequence<Dafny.Rune> _766_name = _source25.dtor_name;
          unmatched25 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod "), _766_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      if (unmatched25) {
        Dafny.ISequence<Dafny.Rune> _767_name = _source25.dtor_name;
        Dafny.ISequence<RAST._IModDecl> _768_body = _source25.dtor_body;
        unmatched25 = false;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod "), _767_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv23), RAST.__default.IND), RAST.__default.SeqToString<RAST._IModDecl>(_768_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IModDecl, Dafny.ISequence<Dafny.Rune>>>>((_769_ind) => ((System.Func<RAST._IModDecl, Dafny.ISequence<Dafny.Rune>>)((_770_modDecl) => {
          return (_770_modDecl)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_769_ind, RAST.__default.IND));
        })))(_pat_let_tv24), Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _pat_let_tv25), RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv26), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      }
      throw new System.Exception("unexpected control point");
    }
  }
  public class Mod_Mod : Mod {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<RAST._IModDecl> _i_body;
    public Mod_Mod(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IModDecl> body) : base() {
      this._i_name = name;
      this._i_body = body;
    }
    public override _IMod DowncastClone() {
      if (this is _IMod dt) { return dt; }
      return new Mod_Mod(_i_name, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Mod_Mod;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Mod.Mod";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
  }
  public class Mod_ExternMod : Mod {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public Mod_ExternMod(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._i_name = name;
    }
    public override _IMod DowncastClone() {
      if (this is _IMod dt) { return dt; }
      return new Mod_ExternMod(_i_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Mod_ExternMod;
      return oth != null && object.Equals(this._i_name, oth._i_name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Mod.ExternMod";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public interface _IModDecl {
    bool is_RawDecl { get; }
    bool is_ModDecl { get; }
    bool is_StructDecl { get; }
    bool is_EnumDecl { get; }
    bool is_ImplDecl { get; }
    bool is_TraitDecl { get; }
    Dafny.ISequence<Dafny.Rune> dtor_body { get; }
    RAST._IMod dtor_mod { get; }
    RAST._IStruct dtor_struct { get; }
    RAST._IEnum dtor_enum { get; }
    RAST._IImpl dtor_impl { get; }
    RAST._ITrait dtor_tr { get; }
    _IModDecl DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public abstract class ModDecl : _IModDecl {
    public ModDecl() {
    }
    private static readonly RAST._IModDecl theDefault = create_RawDecl(Dafny.Sequence<Dafny.Rune>.Empty);
    public static RAST._IModDecl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IModDecl> _TYPE = new Dafny.TypeDescriptor<RAST._IModDecl>(RAST.ModDecl.Default());
    public static Dafny.TypeDescriptor<RAST._IModDecl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IModDecl create_RawDecl(Dafny.ISequence<Dafny.Rune> body) {
      return new ModDecl_RawDecl(body);
    }
    public static _IModDecl create_ModDecl(RAST._IMod mod) {
      return new ModDecl_ModDecl(mod);
    }
    public static _IModDecl create_StructDecl(RAST._IStruct @struct) {
      return new ModDecl_StructDecl(@struct);
    }
    public static _IModDecl create_EnumDecl(RAST._IEnum @enum) {
      return new ModDecl_EnumDecl(@enum);
    }
    public static _IModDecl create_ImplDecl(RAST._IImpl impl) {
      return new ModDecl_ImplDecl(impl);
    }
    public static _IModDecl create_TraitDecl(RAST._ITrait tr) {
      return new ModDecl_TraitDecl(tr);
    }
    public bool is_RawDecl { get { return this is ModDecl_RawDecl; } }
    public bool is_ModDecl { get { return this is ModDecl_ModDecl; } }
    public bool is_StructDecl { get { return this is ModDecl_StructDecl; } }
    public bool is_EnumDecl { get { return this is ModDecl_EnumDecl; } }
    public bool is_ImplDecl { get { return this is ModDecl_ImplDecl; } }
    public bool is_TraitDecl { get { return this is ModDecl_TraitDecl; } }
    public Dafny.ISequence<Dafny.Rune> dtor_body {
      get {
        var d = this;
        return ((ModDecl_RawDecl)d)._i_body;
      }
    }
    public RAST._IMod dtor_mod {
      get {
        var d = this;
        return ((ModDecl_ModDecl)d)._i_mod;
      }
    }
    public RAST._IStruct dtor_struct {
      get {
        var d = this;
        return ((ModDecl_StructDecl)d)._i_struct;
      }
    }
    public RAST._IEnum dtor_enum {
      get {
        var d = this;
        return ((ModDecl_EnumDecl)d)._i_enum;
      }
    }
    public RAST._IImpl dtor_impl {
      get {
        var d = this;
        return ((ModDecl_ImplDecl)d)._i_impl;
      }
    }
    public RAST._ITrait dtor_tr {
      get {
        var d = this;
        return ((ModDecl_TraitDecl)d)._i_tr;
      }
    }
    public abstract _IModDecl DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      if ((this).is_ModDecl) {
        return ((this).dtor_mod)._ToString(ind);
      } else if ((this).is_StructDecl) {
        return ((this).dtor_struct)._ToString(ind);
      } else if ((this).is_ImplDecl) {
        return ((this).dtor_impl)._ToString(ind);
      } else if ((this).is_EnumDecl) {
        return ((this).dtor_enum)._ToString(ind);
      } else if ((this).is_TraitDecl) {
        return ((this).dtor_tr)._ToString(ind);
      } else {
        return (this).dtor_body;
      }
    }
  }
  public class ModDecl_RawDecl : ModDecl {
    public readonly Dafny.ISequence<Dafny.Rune> _i_body;
    public ModDecl_RawDecl(Dafny.ISequence<Dafny.Rune> body) : base() {
      this._i_body = body;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_RawDecl(_i_body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_RawDecl;
      return oth != null && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.RawDecl";
      s += "(";
      s += this._i_body.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ModDecl_ModDecl : ModDecl {
    public readonly RAST._IMod _i_mod;
    public ModDecl_ModDecl(RAST._IMod mod) : base() {
      this._i_mod = mod;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_ModDecl(_i_mod);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_ModDecl;
      return oth != null && object.Equals(this._i_mod, oth._i_mod);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_mod));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.ModDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_mod);
      s += ")";
      return s;
    }
  }
  public class ModDecl_StructDecl : ModDecl {
    public readonly RAST._IStruct _i_struct;
    public ModDecl_StructDecl(RAST._IStruct @struct) : base() {
      this._i_struct = @struct;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_StructDecl(_i_struct);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_StructDecl;
      return oth != null && object.Equals(this._i_struct, oth._i_struct);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_struct));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.StructDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_struct);
      s += ")";
      return s;
    }
  }
  public class ModDecl_EnumDecl : ModDecl {
    public readonly RAST._IEnum _i_enum;
    public ModDecl_EnumDecl(RAST._IEnum @enum) : base() {
      this._i_enum = @enum;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_EnumDecl(_i_enum);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_EnumDecl;
      return oth != null && object.Equals(this._i_enum, oth._i_enum);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_enum));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.EnumDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_enum);
      s += ")";
      return s;
    }
  }
  public class ModDecl_ImplDecl : ModDecl {
    public readonly RAST._IImpl _i_impl;
    public ModDecl_ImplDecl(RAST._IImpl impl) : base() {
      this._i_impl = impl;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_ImplDecl(_i_impl);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_ImplDecl;
      return oth != null && object.Equals(this._i_impl, oth._i_impl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_impl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.ImplDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_impl);
      s += ")";
      return s;
    }
  }
  public class ModDecl_TraitDecl : ModDecl {
    public readonly RAST._ITrait _i_tr;
    public ModDecl_TraitDecl(RAST._ITrait tr) : base() {
      this._i_tr = tr;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_TraitDecl(_i_tr);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_TraitDecl;
      return oth != null && object.Equals(this._i_tr, oth._i_tr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_tr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.TraitDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_tr);
      s += ")";
      return s;
    }
  }

  public interface _IAttribute {
    bool is_RawAttribute { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
  }
  public class Attribute : _IAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _i_content;
    public Attribute(Dafny.ISequence<Dafny.Rune> content) {
      this._i_content = content;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Attribute;
      return oth != null && object.Equals(this._i_content, oth._i_content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Attribute.RawAttribute";
      s += "(";
      s += this._i_content.ToVerbatimString(true);
      s += ")";
      return s;
    }
    private static readonly Dafny.ISequence<Dafny.Rune> theDefault = Dafny.Sequence<Dafny.Rune>.Empty;
    public static Dafny.ISequence<Dafny.Rune> Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAttribute create(Dafny.ISequence<Dafny.Rune> content) {
      return new Attribute(content);
    }
    public static _IAttribute create_RawAttribute(Dafny.ISequence<Dafny.Rune> content) {
      return create(content);
    }
    public bool is_RawAttribute { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_content {
      get {
        return this._i_content;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ToStringMultiple(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> ind)
    {
      return RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(attributes, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>>((_771_ind) => ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_772_attribute) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_772_attribute), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _771_ind);
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
    }
  }

  public interface _IStruct {
    bool is_Struct { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParam> dtor_typeParams { get; }
    RAST._IFormals dtor_fields { get; }
    _IStruct DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Struct : _IStruct {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<RAST._ITypeParam> _i_typeParams;
    public readonly RAST._IFormals _i_fields;
    public Struct(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IFormals fields) {
      this._i_attributes = attributes;
      this._i_name = name;
      this._i_typeParams = typeParams;
      this._i_fields = fields;
    }
    public _IStruct DowncastClone() {
      if (this is _IStruct dt) { return dt; }
      return new Struct(_i_attributes, _i_name, _i_typeParams, _i_fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Struct;
      return oth != null && object.Equals(this._i_attributes, oth._i_attributes) && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_fields, oth._i_fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Struct.Struct";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_attributes);
      s += ", ";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_fields);
      s += ")";
      return s;
    }
    private static readonly RAST._IStruct theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParam>.Empty, RAST.Formals.Default());
    public static RAST._IStruct Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IStruct> _TYPE = new Dafny.TypeDescriptor<RAST._IStruct>(RAST.Struct.Default());
    public static Dafny.TypeDescriptor<RAST._IStruct> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStruct create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IFormals fields) {
      return new Struct(attributes, name, typeParams, fields);
    }
    public static _IStruct create_Struct(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IFormals fields) {
      return create(attributes, name, typeParams, fields);
    }
    public bool is_Struct { get { return true; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_attributes {
      get {
        return this._i_attributes;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParam> dtor_typeParams {
      get {
        return this._i_typeParams;
      }
    }
    public RAST._IFormals dtor_fields {
      get {
        return this._i_fields;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub struct ")), (this).dtor_name), RAST.TypeParam.ToStringMultiple((this).dtor_typeParams, ind)), ((this).dtor_fields)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND), ((this).dtor_fields).is_NamedFormals)), ((((this).dtor_fields).is_NamelessFormals) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
    }
  }

  public interface _INamelessFormal {
    bool is_NamelessFormal { get; }
    RAST._IVisibility dtor_visibility { get; }
    RAST._IType dtor_tpe { get; }
    _INamelessFormal DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class NamelessFormal : _INamelessFormal {
    public readonly RAST._IVisibility _i_visibility;
    public readonly RAST._IType _i_tpe;
    public NamelessFormal(RAST._IVisibility visibility, RAST._IType tpe) {
      this._i_visibility = visibility;
      this._i_tpe = tpe;
    }
    public _INamelessFormal DowncastClone() {
      if (this is _INamelessFormal dt) { return dt; }
      return new NamelessFormal(_i_visibility, _i_tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.NamelessFormal;
      return oth != null && object.Equals(this._i_visibility, oth._i_visibility) && object.Equals(this._i_tpe, oth._i_tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_visibility));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.NamelessFormal.NamelessFormal";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_tpe);
      s += ")";
      return s;
    }
    private static readonly RAST._INamelessFormal theDefault = create(RAST.Visibility.Default(), RAST.Type.Default());
    public static RAST._INamelessFormal Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._INamelessFormal> _TYPE = new Dafny.TypeDescriptor<RAST._INamelessFormal>(RAST.NamelessFormal.Default());
    public static Dafny.TypeDescriptor<RAST._INamelessFormal> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INamelessFormal create(RAST._IVisibility visibility, RAST._IType tpe) {
      return new NamelessFormal(visibility, tpe);
    }
    public static _INamelessFormal create_NamelessFormal(RAST._IVisibility visibility, RAST._IType tpe) {
      return create(visibility, tpe);
    }
    public bool is_NamelessFormal { get { return true; } }
    public RAST._IVisibility dtor_visibility {
      get {
        return this._i_visibility;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._i_tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(((object.Equals((this).dtor_visibility, RAST.Visibility.create_PUB())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub ")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), ((this).dtor_tpe)._ToString(ind));
    }
  }

  public interface _IFormals {
    bool is_NamedFormals { get; }
    bool is_NamelessFormals { get; }
    Dafny.ISequence<RAST._IFormal> dtor_fields { get; }
    Dafny.ISequence<RAST._INamelessFormal> dtor_types { get; }
    _IFormals DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine);
  }
  public abstract class Formals : _IFormals {
    public Formals() {
    }
    private static readonly RAST._IFormals theDefault = create_NamedFormals(Dafny.Sequence<RAST._IFormal>.Empty);
    public static RAST._IFormals Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IFormals> _TYPE = new Dafny.TypeDescriptor<RAST._IFormals>(RAST.Formals.Default());
    public static Dafny.TypeDescriptor<RAST._IFormals> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFormals create_NamedFormals(Dafny.ISequence<RAST._IFormal> fields) {
      return new Formals_NamedFormals(fields);
    }
    public static _IFormals create_NamelessFormals(Dafny.ISequence<RAST._INamelessFormal> types) {
      return new Formals_NamelessFormals(types);
    }
    public bool is_NamedFormals { get { return this is Formals_NamedFormals; } }
    public bool is_NamelessFormals { get { return this is Formals_NamelessFormals; } }
    public Dafny.ISequence<RAST._IFormal> dtor_fields {
      get {
        var d = this;
        return ((Formals_NamedFormals)d)._i_fields;
      }
    }
    public Dafny.ISequence<RAST._INamelessFormal> dtor_types {
      get {
        var d = this;
        return ((Formals_NamelessFormals)d)._i_types;
      }
    }
    public abstract _IFormals DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine)
    {
      if ((this).is_NamedFormals) {
        Dafny.ISequence<Dafny.Rune> _773_separator = ((newLine) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")));
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs40 = (((newLine) && ((new BigInteger(((this).dtor_fields).Count)).Sign == 1)) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind))) : ((((new BigInteger(((this).dtor_fields).Count)).Sign == 1) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))) : (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
        Dafny.ISequence<Dafny.Rune> _774_beginSpace = _let_tmp_rhs40.dtor__0;
        Dafny.ISequence<Dafny.Rune> _775_endSpace = _let_tmp_rhs40.dtor__1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"), _774_beginSpace), RAST.__default.SeqToString<RAST._IFormal>((this).dtor_fields, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>>>((_776_ind) => ((System.Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>)((_777_field) => {
          return (_777_field)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_776_ind, RAST.__default.IND));
        })))(ind), _773_separator)), _775_endSpace), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else {
        Dafny.ISequence<Dafny.Rune> _778_separator = ((newLine) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")));
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._INamelessFormal>((this).dtor_types, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._INamelessFormal, Dafny.ISequence<Dafny.Rune>>>>((_779_ind) => ((System.Func<RAST._INamelessFormal, Dafny.ISequence<Dafny.Rune>>)((_780_t) => {
          return (_780_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_779_ind, RAST.__default.IND));
        })))(ind), _778_separator)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
    }
  }
  public class Formals_NamedFormals : Formals {
    public readonly Dafny.ISequence<RAST._IFormal> _i_fields;
    public Formals_NamedFormals(Dafny.ISequence<RAST._IFormal> fields) : base() {
      this._i_fields = fields;
    }
    public override _IFormals DowncastClone() {
      if (this is _IFormals dt) { return dt; }
      return new Formals_NamedFormals(_i_fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Formals_NamedFormals;
      return oth != null && object.Equals(this._i_fields, oth._i_fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Formals.NamedFormals";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_fields);
      s += ")";
      return s;
    }
  }
  public class Formals_NamelessFormals : Formals {
    public readonly Dafny.ISequence<RAST._INamelessFormal> _i_types;
    public Formals_NamelessFormals(Dafny.ISequence<RAST._INamelessFormal> types) : base() {
      this._i_types = types;
    }
    public override _IFormals DowncastClone() {
      if (this is _IFormals dt) { return dt; }
      return new Formals_NamelessFormals(_i_types);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Formals_NamelessFormals;
      return oth != null && object.Equals(this._i_types, oth._i_types);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_types));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Formals.NamelessFormals";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_types);
      s += ")";
      return s;
    }
  }

  public interface _IEnumCase {
    bool is_EnumCase { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IFormals dtor_fields { get; }
    _IEnumCase DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine);
  }
  public class EnumCase : _IEnumCase {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly RAST._IFormals _i_fields;
    public EnumCase(Dafny.ISequence<Dafny.Rune> name, RAST._IFormals fields) {
      this._i_name = name;
      this._i_fields = fields;
    }
    public _IEnumCase DowncastClone() {
      if (this is _IEnumCase dt) { return dt; }
      return new EnumCase(_i_name, _i_fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.EnumCase;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_fields, oth._i_fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.EnumCase.EnumCase";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_fields);
      s += ")";
      return s;
    }
    private static readonly RAST._IEnumCase theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, RAST.Formals.Default());
    public static RAST._IEnumCase Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IEnumCase> _TYPE = new Dafny.TypeDescriptor<RAST._IEnumCase>(RAST.EnumCase.Default());
    public static Dafny.TypeDescriptor<RAST._IEnumCase> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnumCase create(Dafny.ISequence<Dafny.Rune> name, RAST._IFormals fields) {
      return new EnumCase(name, fields);
    }
    public static _IEnumCase create_EnumCase(Dafny.ISequence<Dafny.Rune> name, RAST._IFormals fields) {
      return create(name, fields);
    }
    public bool is_EnumCase { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public RAST._IFormals dtor_fields {
      get {
        return this._i_fields;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine)
    {
      return Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_name, ((this).dtor_fields)._ToString(ind, newLine));
    }
  }

  public interface _IEnum {
    bool is_Enum { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParam> dtor_typeParams { get; }
    Dafny.ISequence<RAST._IEnumCase> dtor_variants { get; }
    _IEnum DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Enum : _IEnum {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<RAST._ITypeParam> _i_typeParams;
    public readonly Dafny.ISequence<RAST._IEnumCase> _i_variants;
    public Enum(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
      this._i_attributes = attributes;
      this._i_name = name;
      this._i_typeParams = typeParams;
      this._i_variants = variants;
    }
    public _IEnum DowncastClone() {
      if (this is _IEnum dt) { return dt; }
      return new Enum(_i_attributes, _i_name, _i_typeParams, _i_variants);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Enum;
      return oth != null && object.Equals(this._i_attributes, oth._i_attributes) && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_variants, oth._i_variants);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_variants));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Enum.Enum";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_attributes);
      s += ", ";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_variants);
      s += ")";
      return s;
    }
    private static readonly RAST._IEnum theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParam>.Empty, Dafny.Sequence<RAST._IEnumCase>.Empty);
    public static RAST._IEnum Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IEnum> _TYPE = new Dafny.TypeDescriptor<RAST._IEnum>(RAST.Enum.Default());
    public static Dafny.TypeDescriptor<RAST._IEnum> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnum create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
      return new Enum(attributes, name, typeParams, variants);
    }
    public static _IEnum create_Enum(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
      return create(attributes, name, typeParams, variants);
    }
    public bool is_Enum { get { return true; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_attributes {
      get {
        return this._i_attributes;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParam> dtor_typeParams {
      get {
        return this._i_typeParams;
      }
    }
    public Dafny.ISequence<RAST._IEnumCase> dtor_variants {
      get {
        return this._i_variants;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub enum ")), (this).dtor_name), RAST.TypeParam.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IEnumCase>((this).dtor_variants, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IEnumCase, Dafny.ISequence<Dafny.Rune>>>>((_781_ind) => ((System.Func<RAST._IEnumCase, Dafny.ISequence<Dafny.Rune>>)((_782_variant) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _781_ind), RAST.__default.IND), (_782_variant)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_781_ind, RAST.__default.IND), false));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }

  public interface _ITypeParam {
    bool is_RawTypeParam { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
    Dafny.ISequence<RAST._IType> dtor_constraints { get; }
    _ITypeParam DowncastClone();
    RAST._ITypeParam AddConstraints(Dafny.ISequence<RAST._IType> constraints);
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class TypeParam : _ITypeParam {
    public readonly Dafny.ISequence<Dafny.Rune> _i_content;
    public readonly Dafny.ISequence<RAST._IType> _i_constraints;
    public TypeParam(Dafny.ISequence<Dafny.Rune> content, Dafny.ISequence<RAST._IType> constraints) {
      this._i_content = content;
      this._i_constraints = constraints;
    }
    public _ITypeParam DowncastClone() {
      if (this is _ITypeParam dt) { return dt; }
      return new TypeParam(_i_content, _i_constraints);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.TypeParam;
      return oth != null && object.Equals(this._i_content, oth._i_content) && object.Equals(this._i_constraints, oth._i_constraints);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_content));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_constraints));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.TypeParam.RawTypeParam";
      s += "(";
      s += this._i_content.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_constraints);
      s += ")";
      return s;
    }
    private static readonly RAST._ITypeParam theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IType>.Empty);
    public static RAST._ITypeParam Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITypeParam> _TYPE = new Dafny.TypeDescriptor<RAST._ITypeParam>(RAST.TypeParam.Default());
    public static Dafny.TypeDescriptor<RAST._ITypeParam> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITypeParam create(Dafny.ISequence<Dafny.Rune> content, Dafny.ISequence<RAST._IType> constraints) {
      return new TypeParam(content, constraints);
    }
    public static _ITypeParam create_RawTypeParam(Dafny.ISequence<Dafny.Rune> content, Dafny.ISequence<RAST._IType> constraints) {
      return create(content, constraints);
    }
    public bool is_RawTypeParam { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_content {
      get {
        return this._i_content;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_constraints {
      get {
        return this._i_constraints;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ToStringMultiple(Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<Dafny.Rune> ind)
    {
      if ((new BigInteger((typeParams).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), RAST.__default.SeqToString<RAST._ITypeParam>(typeParams, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._ITypeParam, Dafny.ISequence<Dafny.Rune>>>>((_783_ind) => ((System.Func<RAST._ITypeParam, Dafny.ISequence<Dafny.Rune>>)((_784_t) => {
          return (_784_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_783_ind, RAST.__default.IND));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
    }
    public static Dafny.ISequence<RAST._ITypeParam> AddConstraintsMultiple(Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IType> constraints)
    {
      Dafny.ISequence<RAST._ITypeParam> _785___accumulator = Dafny.Sequence<RAST._ITypeParam>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((typeParams).Count)).Sign == 0) {
        return Dafny.Sequence<RAST._ITypeParam>.Concat(_785___accumulator, Dafny.Sequence<RAST._ITypeParam>.FromElements());
      } else {
        _785___accumulator = Dafny.Sequence<RAST._ITypeParam>.Concat(_785___accumulator, Dafny.Sequence<RAST._ITypeParam>.FromElements(((typeParams).Select(BigInteger.Zero)).AddConstraints(constraints)));
        Dafny.ISequence<RAST._ITypeParam> _in111 = (typeParams).Drop(BigInteger.One);
        Dafny.ISequence<RAST._IType> _in112 = constraints;
        typeParams = _in111;
        constraints = _in112;
        goto TAIL_CALL_START;
      }
    }
    public RAST._ITypeParam AddConstraints(Dafny.ISequence<RAST._IType> constraints) {
      RAST._ITypeParam _786_dt__update__tmp_h0 = this;
      Dafny.ISequence<RAST._IType> _787_dt__update_hconstraints_h0 = Dafny.Sequence<RAST._IType>.Concat((this).dtor_constraints, constraints);
      return RAST.TypeParam.create((_786_dt__update__tmp_h0).dtor_content, _787_dt__update_hconstraints_h0);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_content, (((new BigInteger(((this).dtor_constraints).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), RAST.__default.SeqToString<RAST._IType>((this).dtor_constraints, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_788_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_789_t) => {
        return (_789_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_788_ind, RAST.__default.IND));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + "))))));
    }
  }

  public interface _IType {
    bool is_SelfOwned { get; }
    bool is_U8 { get; }
    bool is_U16 { get; }
    bool is_U32 { get; }
    bool is_U64 { get; }
    bool is_U128 { get; }
    bool is_I8 { get; }
    bool is_I16 { get; }
    bool is_I32 { get; }
    bool is_I64 { get; }
    bool is_I128 { get; }
    bool is_TIdentifier { get; }
    bool is_TMemberSelect { get; }
    bool is_TypeApp { get; }
    bool is_Borrowed { get; }
    bool is_BorrowedMut { get; }
    bool is_ImplType { get; }
    bool is_DynType { get; }
    bool is_TupleType { get; }
    bool is_FnType { get; }
    bool is_IntersectionType { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IType dtor_base { get; }
    RAST._IType dtor_baseName { get; }
    Dafny.ISequence<RAST._IType> dtor_arguments { get; }
    RAST._IType dtor_underlying { get; }
    RAST._IType dtor_returnType { get; }
    RAST._IType dtor_left { get; }
    RAST._IType dtor_right { get; }
    _IType DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
    RAST._IType MSel(Dafny.ISequence<Dafny.Rune> name);
    RAST._IType Apply1(RAST._IType arg);
  }
  public abstract class Type : _IType {
    public Type() {
    }
    private static readonly RAST._IType theDefault = create_SelfOwned();
    public static RAST._IType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IType> _TYPE = new Dafny.TypeDescriptor<RAST._IType>(RAST.Type.Default());
    public static Dafny.TypeDescriptor<RAST._IType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IType create_SelfOwned() {
      return new Type_SelfOwned();
    }
    public static _IType create_U8() {
      return new Type_U8();
    }
    public static _IType create_U16() {
      return new Type_U16();
    }
    public static _IType create_U32() {
      return new Type_U32();
    }
    public static _IType create_U64() {
      return new Type_U64();
    }
    public static _IType create_U128() {
      return new Type_U128();
    }
    public static _IType create_I8() {
      return new Type_I8();
    }
    public static _IType create_I16() {
      return new Type_I16();
    }
    public static _IType create_I32() {
      return new Type_I32();
    }
    public static _IType create_I64() {
      return new Type_I64();
    }
    public static _IType create_I128() {
      return new Type_I128();
    }
    public static _IType create_TIdentifier(Dafny.ISequence<Dafny.Rune> name) {
      return new Type_TIdentifier(name);
    }
    public static _IType create_TMemberSelect(RAST._IType @base, Dafny.ISequence<Dafny.Rune> name) {
      return new Type_TMemberSelect(@base, name);
    }
    public static _IType create_TypeApp(RAST._IType baseName, Dafny.ISequence<RAST._IType> arguments) {
      return new Type_TypeApp(baseName, arguments);
    }
    public static _IType create_Borrowed(RAST._IType underlying) {
      return new Type_Borrowed(underlying);
    }
    public static _IType create_BorrowedMut(RAST._IType underlying) {
      return new Type_BorrowedMut(underlying);
    }
    public static _IType create_ImplType(RAST._IType underlying) {
      return new Type_ImplType(underlying);
    }
    public static _IType create_DynType(RAST._IType underlying) {
      return new Type_DynType(underlying);
    }
    public static _IType create_TupleType(Dafny.ISequence<RAST._IType> arguments) {
      return new Type_TupleType(arguments);
    }
    public static _IType create_FnType(Dafny.ISequence<RAST._IType> arguments, RAST._IType returnType) {
      return new Type_FnType(arguments, returnType);
    }
    public static _IType create_IntersectionType(RAST._IType left, RAST._IType right) {
      return new Type_IntersectionType(left, right);
    }
    public bool is_SelfOwned { get { return this is Type_SelfOwned; } }
    public bool is_U8 { get { return this is Type_U8; } }
    public bool is_U16 { get { return this is Type_U16; } }
    public bool is_U32 { get { return this is Type_U32; } }
    public bool is_U64 { get { return this is Type_U64; } }
    public bool is_U128 { get { return this is Type_U128; } }
    public bool is_I8 { get { return this is Type_I8; } }
    public bool is_I16 { get { return this is Type_I16; } }
    public bool is_I32 { get { return this is Type_I32; } }
    public bool is_I64 { get { return this is Type_I64; } }
    public bool is_I128 { get { return this is Type_I128; } }
    public bool is_TIdentifier { get { return this is Type_TIdentifier; } }
    public bool is_TMemberSelect { get { return this is Type_TMemberSelect; } }
    public bool is_TypeApp { get { return this is Type_TypeApp; } }
    public bool is_Borrowed { get { return this is Type_Borrowed; } }
    public bool is_BorrowedMut { get { return this is Type_BorrowedMut; } }
    public bool is_ImplType { get { return this is Type_ImplType; } }
    public bool is_DynType { get { return this is Type_DynType; } }
    public bool is_TupleType { get { return this is Type_TupleType; } }
    public bool is_FnType { get { return this is Type_FnType; } }
    public bool is_IntersectionType { get { return this is Type_IntersectionType; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Type_TIdentifier) { return ((Type_TIdentifier)d)._i_name; }
        return ((Type_TMemberSelect)d)._i_name;
      }
    }
    public RAST._IType dtor_base {
      get {
        var d = this;
        return ((Type_TMemberSelect)d)._i_base;
      }
    }
    public RAST._IType dtor_baseName {
      get {
        var d = this;
        return ((Type_TypeApp)d)._i_baseName;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_arguments {
      get {
        var d = this;
        if (d is Type_TypeApp) { return ((Type_TypeApp)d)._i_arguments; }
        if (d is Type_TupleType) { return ((Type_TupleType)d)._i_arguments; }
        return ((Type_FnType)d)._i_arguments;
      }
    }
    public RAST._IType dtor_underlying {
      get {
        var d = this;
        if (d is Type_Borrowed) { return ((Type_Borrowed)d)._i_underlying; }
        if (d is Type_BorrowedMut) { return ((Type_BorrowedMut)d)._i_underlying; }
        if (d is Type_ImplType) { return ((Type_ImplType)d)._i_underlying; }
        return ((Type_DynType)d)._i_underlying;
      }
    }
    public RAST._IType dtor_returnType {
      get {
        var d = this;
        return ((Type_FnType)d)._i_returnType;
      }
    }
    public RAST._IType dtor_left {
      get {
        var d = this;
        return ((Type_IntersectionType)d)._i_left;
      }
    }
    public RAST._IType dtor_right {
      get {
        var d = this;
        return ((Type_IntersectionType)d)._i_right;
      }
    }
    public abstract _IType DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      var _pat_let_tv27 = ind;
      var _pat_let_tv28 = ind;
      var _pat_let_tv29 = ind;
      var _pat_let_tv30 = ind;
      var _pat_let_tv31 = ind;
      var _pat_let_tv32 = ind;
      var _pat_let_tv33 = ind;
      var _pat_let_tv34 = ind;
      var _pat_let_tv35 = ind;
      var _pat_let_tv36 = ind;
      var _pat_let_tv37 = ind;
      var _pat_let_tv38 = ind;
      RAST._IType _source26 = this;
      bool unmatched26 = true;
      if (unmatched26) {
        if (_source26.is_TIdentifier) {
          Dafny.ISequence<Dafny.Rune> _790_underlying = _source26.dtor_name;
          unmatched26 = false;
          return _790_underlying;
        }
      }
      if (unmatched26) {
        if (_source26.is_TMemberSelect) {
          RAST._IType _791_underlying = _source26.dtor_base;
          Dafny.ISequence<Dafny.Rune> _792_name = _source26.dtor_name;
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_791_underlying)._ToString(_pat_let_tv27), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _792_name);
        }
      }
      if (unmatched26) {
        if (_source26.is_Borrowed) {
          RAST._IType _793_underlying = _source26.dtor_underlying;
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), (_793_underlying)._ToString(_pat_let_tv28));
        }
      }
      if (unmatched26) {
        if (_source26.is_BorrowedMut) {
          RAST._IType _794_underlying = _source26.dtor_underlying;
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut "), (_794_underlying)._ToString(_pat_let_tv29));
        }
      }
      if (unmatched26) {
        if (_source26.is_ImplType) {
          RAST._IType _795_underlying = _source26.dtor_underlying;
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), (_795_underlying)._ToString(_pat_let_tv30));
        }
      }
      if (unmatched26) {
        if (_source26.is_DynType) {
          RAST._IType _796_underlying = _source26.dtor_underlying;
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn "), (_796_underlying)._ToString(_pat_let_tv31));
        }
      }
      if (unmatched26) {
        if (_source26.is_FnType) {
          Dafny.ISequence<RAST._IType> _797_arguments = _source26.dtor_arguments;
          RAST._IType _798_returnType = _source26.dtor_returnType;
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Fn("), RAST.__default.SeqToString<RAST._IType>(_797_arguments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_799_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_800_arg) => {
            return (_800_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_799_ind, RAST.__default.IND));
          })))(_pat_let_tv32), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), (_798_returnType)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv33, RAST.__default.IND)));
        }
      }
      if (unmatched26) {
        if (_source26.is_IntersectionType) {
          RAST._IType _801_left = _source26.dtor_left;
          RAST._IType _802_right = _source26.dtor_right;
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_801_left)._ToString(_pat_let_tv34), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + ")), (_802_right)._ToString(_pat_let_tv35));
        }
      }
      if (unmatched26) {
        if (_source26.is_TupleType) {
          Dafny.ISequence<RAST._IType> _803_args = _source26.dtor_arguments;
          unmatched26 = false;
          if ((_803_args).Equals(Dafny.Sequence<RAST._IType>.FromElements())) {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()");
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._IType>(_803_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_804_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_805_arg) => {
              return (_805_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_804_ind, RAST.__default.IND));
            })))(_pat_let_tv36), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
        }
      }
      if (unmatched26) {
        if (_source26.is_TypeApp) {
          RAST._IType _806_base = _source26.dtor_baseName;
          Dafny.ISequence<RAST._IType> _807_args = _source26.dtor_arguments;
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat((_806_base)._ToString(_pat_let_tv37), (((_807_args).Equals(Dafny.Sequence<RAST._IType>.FromElements())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), RAST.__default.SeqToString<RAST._IType>(_807_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_808_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_809_arg) => {
            return (_809_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_808_ind, RAST.__default.IND));
          })))(_pat_let_tv38), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">")))));
        }
      }
      if (unmatched26) {
        if (_source26.is_SelfOwned) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
        }
      }
      if (unmatched26) {
        if (_source26.is_U8) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8");
        }
      }
      if (unmatched26) {
        if (_source26.is_U16) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16");
        }
      }
      if (unmatched26) {
        if (_source26.is_U32) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32");
        }
      }
      if (unmatched26) {
        if (_source26.is_U64) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64");
        }
      }
      if (unmatched26) {
        if (_source26.is_U128) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128");
        }
      }
      if (unmatched26) {
        if (_source26.is_I8) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8");
        }
      }
      if (unmatched26) {
        if (_source26.is_I16) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16");
        }
      }
      if (unmatched26) {
        if (_source26.is_I32) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32");
        }
      }
      if (unmatched26) {
        if (_source26.is_I64) {
          unmatched26 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64");
        }
      }
      if (unmatched26) {
        unmatched26 = false;
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128");
      }
      throw new System.Exception("unexpected control point");
    }
    public RAST._IType MSel(Dafny.ISequence<Dafny.Rune> name) {
      return RAST.Type.create_TMemberSelect(this, name);
    }
    public RAST._IType Apply1(RAST._IType arg) {
      return RAST.Type.create_TypeApp(this, Dafny.Sequence<RAST._IType>.FromElements(arg));
    }
  }
  public class Type_SelfOwned : Type {
    public Type_SelfOwned() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_SelfOwned();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_SelfOwned;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.SelfOwned";
      return s;
    }
  }
  public class Type_U8 : Type {
    public Type_U8() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U8();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U8;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U8";
      return s;
    }
  }
  public class Type_U16 : Type {
    public Type_U16() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U16();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U16";
      return s;
    }
  }
  public class Type_U32 : Type {
    public Type_U32() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U32();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U32;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U32";
      return s;
    }
  }
  public class Type_U64 : Type {
    public Type_U64() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U64();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U64;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U64";
      return s;
    }
  }
  public class Type_U128 : Type {
    public Type_U128() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U128();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U128;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U128";
      return s;
    }
  }
  public class Type_I8 : Type {
    public Type_I8() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I8();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I8;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I8";
      return s;
    }
  }
  public class Type_I16 : Type {
    public Type_I16() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I16();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I16";
      return s;
    }
  }
  public class Type_I32 : Type {
    public Type_I32() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I32();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I32;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I32";
      return s;
    }
  }
  public class Type_I64 : Type {
    public Type_I64() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I64();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I64;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I64";
      return s;
    }
  }
  public class Type_I128 : Type {
    public Type_I128() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I128();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I128;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I128";
      return s;
    }
  }
  public class Type_TIdentifier : Type {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public Type_TIdentifier(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._i_name = name;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TIdentifier(_i_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TIdentifier;
      return oth != null && object.Equals(this._i_name, oth._i_name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TIdentifier";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Type_TMemberSelect : Type {
    public readonly RAST._IType _i_base;
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public Type_TMemberSelect(RAST._IType @base, Dafny.ISequence<Dafny.Rune> name) : base() {
      this._i_base = @base;
      this._i_name = name;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TMemberSelect(_i_base, _i_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TMemberSelect;
      return oth != null && object.Equals(this._i_base, oth._i_base) && object.Equals(this._i_name, oth._i_name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_base));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TMemberSelect";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_base);
      s += ", ";
      s += this._i_name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Type_TypeApp : Type {
    public readonly RAST._IType _i_baseName;
    public readonly Dafny.ISequence<RAST._IType> _i_arguments;
    public Type_TypeApp(RAST._IType baseName, Dafny.ISequence<RAST._IType> arguments) : base() {
      this._i_baseName = baseName;
      this._i_arguments = arguments;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TypeApp(_i_baseName, _i_arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TypeApp;
      return oth != null && object.Equals(this._i_baseName, oth._i_baseName) && object.Equals(this._i_arguments, oth._i_arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_baseName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TypeApp";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_baseName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_arguments);
      s += ")";
      return s;
    }
  }
  public class Type_Borrowed : Type {
    public readonly RAST._IType _i_underlying;
    public Type_Borrowed(RAST._IType underlying) : base() {
      this._i_underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Borrowed(_i_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_Borrowed;
      return oth != null && object.Equals(this._i_underlying, oth._i_underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.Borrowed";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_underlying);
      s += ")";
      return s;
    }
  }
  public class Type_BorrowedMut : Type {
    public readonly RAST._IType _i_underlying;
    public Type_BorrowedMut(RAST._IType underlying) : base() {
      this._i_underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_BorrowedMut(_i_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_BorrowedMut;
      return oth != null && object.Equals(this._i_underlying, oth._i_underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.BorrowedMut";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_underlying);
      s += ")";
      return s;
    }
  }
  public class Type_ImplType : Type {
    public readonly RAST._IType _i_underlying;
    public Type_ImplType(RAST._IType underlying) : base() {
      this._i_underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_ImplType(_i_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_ImplType;
      return oth != null && object.Equals(this._i_underlying, oth._i_underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.ImplType";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_underlying);
      s += ")";
      return s;
    }
  }
  public class Type_DynType : Type {
    public readonly RAST._IType _i_underlying;
    public Type_DynType(RAST._IType underlying) : base() {
      this._i_underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_DynType(_i_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_DynType;
      return oth != null && object.Equals(this._i_underlying, oth._i_underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.DynType";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_underlying);
      s += ")";
      return s;
    }
  }
  public class Type_TupleType : Type {
    public readonly Dafny.ISequence<RAST._IType> _i_arguments;
    public Type_TupleType(Dafny.ISequence<RAST._IType> arguments) : base() {
      this._i_arguments = arguments;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TupleType(_i_arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TupleType;
      return oth != null && object.Equals(this._i_arguments, oth._i_arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TupleType";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_arguments);
      s += ")";
      return s;
    }
  }
  public class Type_FnType : Type {
    public readonly Dafny.ISequence<RAST._IType> _i_arguments;
    public readonly RAST._IType _i_returnType;
    public Type_FnType(Dafny.ISequence<RAST._IType> arguments, RAST._IType returnType) : base() {
      this._i_arguments = arguments;
      this._i_returnType = returnType;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_FnType(_i_arguments, _i_returnType);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_FnType;
      return oth != null && object.Equals(this._i_arguments, oth._i_arguments) && object.Equals(this._i_returnType, oth._i_returnType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_arguments));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_returnType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.FnType";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_arguments);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_returnType);
      s += ")";
      return s;
    }
  }
  public class Type_IntersectionType : Type {
    public readonly RAST._IType _i_left;
    public readonly RAST._IType _i_right;
    public Type_IntersectionType(RAST._IType left, RAST._IType right) : base() {
      this._i_left = left;
      this._i_right = right;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_IntersectionType(_i_left, _i_right);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_IntersectionType;
      return oth != null && object.Equals(this._i_left, oth._i_left) && object.Equals(this._i_right, oth._i_right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_right));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.IntersectionType";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_right);
      s += ")";
      return s;
    }
  }

  public interface _ITrait {
    bool is_Trait { get; }
    Dafny.ISequence<RAST._ITypeParam> dtor_typeParams { get; }
    RAST._IType dtor_tpe { get; }
    Dafny.ISequence<Dafny.Rune> dtor_where { get; }
    Dafny.ISequence<RAST._IImplMember> dtor_body { get; }
    _ITrait DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Trait : _ITrait {
    public readonly Dafny.ISequence<RAST._ITypeParam> _i_typeParams;
    public readonly RAST._IType _i_tpe;
    public readonly Dafny.ISequence<Dafny.Rune> _i_where;
    public readonly Dafny.ISequence<RAST._IImplMember> _i_body;
    public Trait(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) {
      this._i_typeParams = typeParams;
      this._i_tpe = tpe;
      this._i_where = @where;
      this._i_body = body;
    }
    public _ITrait DowncastClone() {
      if (this is _ITrait dt) { return dt; }
      return new Trait(_i_typeParams, _i_tpe, _i_where, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Trait;
      return oth != null && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_tpe, oth._i_tpe) && object.Equals(this._i_where, oth._i_where) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_where));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Trait.Trait";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_tpe);
      s += ", ";
      s += this._i_where.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
    private static readonly RAST._ITrait theDefault = create(Dafny.Sequence<RAST._ITypeParam>.Empty, RAST.Type.Default(), Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IImplMember>.Empty);
    public static RAST._ITrait Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITrait> _TYPE = new Dafny.TypeDescriptor<RAST._ITrait>(RAST.Trait.Default());
    public static Dafny.TypeDescriptor<RAST._ITrait> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITrait create(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) {
      return new Trait(typeParams, tpe, @where, body);
    }
    public static _ITrait create_Trait(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) {
      return create(typeParams, tpe, @where, body);
    }
    public bool is_Trait { get { return true; } }
    public Dafny.ISequence<RAST._ITypeParam> dtor_typeParams {
      get {
        return this._i_typeParams;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._i_tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_where {
      get {
        return this._i_where;
      }
    }
    public Dafny.ISequence<RAST._IImplMember> dtor_body {
      get {
        return this._i_body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait "), RAST.TypeParam.ToStringMultiple((this).dtor_typeParams, ind)), ((this).dtor_tpe)._ToString(ind)), ((!((this).dtor_where).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), (this).dtor_where)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IImplMember>((this).dtor_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>>>((_810_ind) => ((System.Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>)((_811_member) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _810_ind), RAST.__default.IND), (_811_member)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_810_ind, RAST.__default.IND)));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (((new BigInteger(((this).dtor_body).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }

  public interface _IImpl {
    bool is_ImplFor { get; }
    bool is_Impl { get; }
    Dafny.ISequence<RAST._ITypeParam> dtor_typeParams { get; }
    RAST._IType dtor_tpe { get; }
    RAST._IType dtor_forType { get; }
    Dafny.ISequence<Dafny.Rune> dtor_where { get; }
    Dafny.ISequence<RAST._IImplMember> dtor_body { get; }
    _IImpl DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public abstract class Impl : _IImpl {
    public Impl() {
    }
    private static readonly RAST._IImpl theDefault = create_ImplFor(Dafny.Sequence<RAST._ITypeParam>.Empty, RAST.Type.Default(), RAST.Type.Default(), Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IImplMember>.Empty);
    public static RAST._IImpl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IImpl> _TYPE = new Dafny.TypeDescriptor<RAST._IImpl>(RAST.Impl.Default());
    public static Dafny.TypeDescriptor<RAST._IImpl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImpl create_ImplFor(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, RAST._IType forType, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) {
      return new Impl_ImplFor(typeParams, tpe, forType, @where, body);
    }
    public static _IImpl create_Impl(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) {
      return new Impl_Impl(typeParams, tpe, @where, body);
    }
    public bool is_ImplFor { get { return this is Impl_ImplFor; } }
    public bool is_Impl { get { return this is Impl_Impl; } }
    public Dafny.ISequence<RAST._ITypeParam> dtor_typeParams {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._i_typeParams; }
        return ((Impl_Impl)d)._i_typeParams;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._i_tpe; }
        return ((Impl_Impl)d)._i_tpe;
      }
    }
    public RAST._IType dtor_forType {
      get {
        var d = this;
        return ((Impl_ImplFor)d)._i_forType;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_where {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._i_where; }
        return ((Impl_Impl)d)._i_where;
      }
    }
    public Dafny.ISequence<RAST._IImplMember> dtor_body {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._i_body; }
        return ((Impl_Impl)d)._i_body;
      }
    }
    public abstract _IImpl DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), RAST.TypeParam.ToStringMultiple((this).dtor_typeParams, ind)), ((this).dtor_tpe)._ToString(ind)), (((this).is_ImplFor) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" for "), ((this).dtor_forType)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), ((!((this).dtor_where).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), (this).dtor_where)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IImplMember>((this).dtor_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>>>((_812_ind) => ((System.Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>)((_813_member) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _812_ind), RAST.__default.IND), (_813_member)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_812_ind, RAST.__default.IND)));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (((new BigInteger(((this).dtor_body).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }
  public class Impl_ImplFor : Impl {
    public readonly Dafny.ISequence<RAST._ITypeParam> _i_typeParams;
    public readonly RAST._IType _i_tpe;
    public readonly RAST._IType _i_forType;
    public readonly Dafny.ISequence<Dafny.Rune> _i_where;
    public readonly Dafny.ISequence<RAST._IImplMember> _i_body;
    public Impl_ImplFor(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, RAST._IType forType, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) : base() {
      this._i_typeParams = typeParams;
      this._i_tpe = tpe;
      this._i_forType = forType;
      this._i_where = @where;
      this._i_body = body;
    }
    public override _IImpl DowncastClone() {
      if (this is _IImpl dt) { return dt; }
      return new Impl_ImplFor(_i_typeParams, _i_tpe, _i_forType, _i_where, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Impl_ImplFor;
      return oth != null && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_tpe, oth._i_tpe) && object.Equals(this._i_forType, oth._i_forType) && object.Equals(this._i_where, oth._i_where) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_forType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_where));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Impl.ImplFor";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_forType);
      s += ", ";
      s += this._i_where.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
  }
  public class Impl_Impl : Impl {
    public readonly Dafny.ISequence<RAST._ITypeParam> _i_typeParams;
    public readonly RAST._IType _i_tpe;
    public readonly Dafny.ISequence<Dafny.Rune> _i_where;
    public readonly Dafny.ISequence<RAST._IImplMember> _i_body;
    public Impl_Impl(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) : base() {
      this._i_typeParams = typeParams;
      this._i_tpe = tpe;
      this._i_where = @where;
      this._i_body = body;
    }
    public override _IImpl DowncastClone() {
      if (this is _IImpl dt) { return dt; }
      return new Impl_Impl(_i_typeParams, _i_tpe, _i_where, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Impl_Impl;
      return oth != null && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_tpe, oth._i_tpe) && object.Equals(this._i_where, oth._i_where) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_where));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Impl.Impl";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_tpe);
      s += ", ";
      s += this._i_where.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
  }

  public interface _IImplMember {
    bool is_RawImplMember { get; }
    bool is_FnDecl { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
    RAST._IVisibility dtor_pub { get; }
    RAST._IFn dtor_fun { get; }
    _IImplMember DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public abstract class ImplMember : _IImplMember {
    public ImplMember() {
    }
    private static readonly RAST._IImplMember theDefault = create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Empty);
    public static RAST._IImplMember Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IImplMember> _TYPE = new Dafny.TypeDescriptor<RAST._IImplMember>(RAST.ImplMember.Default());
    public static Dafny.TypeDescriptor<RAST._IImplMember> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImplMember create_RawImplMember(Dafny.ISequence<Dafny.Rune> content) {
      return new ImplMember_RawImplMember(content);
    }
    public static _IImplMember create_FnDecl(RAST._IVisibility pub, RAST._IFn fun) {
      return new ImplMember_FnDecl(pub, fun);
    }
    public bool is_RawImplMember { get { return this is ImplMember_RawImplMember; } }
    public bool is_FnDecl { get { return this is ImplMember_FnDecl; } }
    public Dafny.ISequence<Dafny.Rune> dtor_content {
      get {
        var d = this;
        return ((ImplMember_RawImplMember)d)._i_content;
      }
    }
    public RAST._IVisibility dtor_pub {
      get {
        var d = this;
        return ((ImplMember_FnDecl)d)._i_pub;
      }
    }
    public RAST._IFn dtor_fun {
      get {
        var d = this;
        return ((ImplMember_FnDecl)d)._i_fun;
      }
    }
    public abstract _IImplMember DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      if ((this).is_FnDecl) {
        return Dafny.Sequence<Dafny.Rune>.Concat(((object.Equals((this).dtor_pub, RAST.Visibility.create_PUB())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub ")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), ((this).dtor_fun)._ToString(ind));
      } else {
        return (this).dtor_content;
      }
    }
  }
  public class ImplMember_RawImplMember : ImplMember {
    public readonly Dafny.ISequence<Dafny.Rune> _i_content;
    public ImplMember_RawImplMember(Dafny.ISequence<Dafny.Rune> content) : base() {
      this._i_content = content;
    }
    public override _IImplMember DowncastClone() {
      if (this is _IImplMember dt) { return dt; }
      return new ImplMember_RawImplMember(_i_content);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ImplMember_RawImplMember;
      return oth != null && object.Equals(this._i_content, oth._i_content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ImplMember.RawImplMember";
      s += "(";
      s += this._i_content.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ImplMember_FnDecl : ImplMember {
    public readonly RAST._IVisibility _i_pub;
    public readonly RAST._IFn _i_fun;
    public ImplMember_FnDecl(RAST._IVisibility pub, RAST._IFn fun) : base() {
      this._i_pub = pub;
      this._i_fun = fun;
    }
    public override _IImplMember DowncastClone() {
      if (this is _IImplMember dt) { return dt; }
      return new ImplMember_FnDecl(_i_pub, _i_fun);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ImplMember_FnDecl;
      return oth != null && object.Equals(this._i_pub, oth._i_pub) && object.Equals(this._i_fun, oth._i_fun);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_pub));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_fun));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ImplMember.FnDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_pub);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_fun);
      s += ")";
      return s;
    }
  }

  public interface _IVisibility {
    bool is_PUB { get; }
    bool is_PRIV { get; }
    _IVisibility DowncastClone();
  }
  public abstract class Visibility : _IVisibility {
    public Visibility() {
    }
    private static readonly RAST._IVisibility theDefault = create_PUB();
    public static RAST._IVisibility Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IVisibility> _TYPE = new Dafny.TypeDescriptor<RAST._IVisibility>(RAST.Visibility.Default());
    public static Dafny.TypeDescriptor<RAST._IVisibility> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IVisibility create_PUB() {
      return new Visibility_PUB();
    }
    public static _IVisibility create_PRIV() {
      return new Visibility_PRIV();
    }
    public bool is_PUB { get { return this is Visibility_PUB; } }
    public bool is_PRIV { get { return this is Visibility_PRIV; } }
    public static System.Collections.Generic.IEnumerable<_IVisibility> AllSingletonConstructors {
      get {
        yield return Visibility.create_PUB();
        yield return Visibility.create_PRIV();
      }
    }
    public abstract _IVisibility DowncastClone();
  }
  public class Visibility_PUB : Visibility {
    public Visibility_PUB() : base() {
    }
    public override _IVisibility DowncastClone() {
      if (this is _IVisibility dt) { return dt; }
      return new Visibility_PUB();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Visibility_PUB;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Visibility.PUB";
      return s;
    }
  }
  public class Visibility_PRIV : Visibility {
    public Visibility_PRIV() : base() {
    }
    public override _IVisibility DowncastClone() {
      if (this is _IVisibility dt) { return dt; }
      return new Visibility_PRIV();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Visibility_PRIV;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Visibility.PRIV";
      return s;
    }
  }

  public interface _IFormal {
    bool is_Formal { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IType dtor_tpe { get; }
    _IFormal DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Formal : _IFormal {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly RAST._IType _i_tpe;
    public Formal(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe) {
      this._i_name = name;
      this._i_tpe = tpe;
    }
    public _IFormal DowncastClone() {
      if (this is _IFormal dt) { return dt; }
      return new Formal(_i_name, _i_tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Formal;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_tpe, oth._i_tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Formal.Formal";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_tpe);
      s += ")";
      return s;
    }
    private static readonly RAST._IFormal theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, RAST.Type.Default());
    public static RAST._IFormal Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IFormal> _TYPE = new Dafny.TypeDescriptor<RAST._IFormal>(RAST.Formal.Default());
    public static Dafny.TypeDescriptor<RAST._IFormal> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFormal create(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe) {
      return new Formal(name, tpe);
    }
    public static _IFormal create_Formal(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe) {
      return create(name, tpe);
    }
    public bool is_Formal { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._i_tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      if ((((this).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) && (((this).dtor_tpe).is_SelfOwned)) {
        return (this).dtor_name;
      } else if ((((this).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self"))) && (object.Equals((this).dtor_tpe, RAST.Type.create_Borrowed(RAST.Type.create_SelfOwned())))) {
        return (this).dtor_name;
      } else if ((((this).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut self"))) && (object.Equals((this).dtor_tpe, RAST.Type.create_Borrowed(RAST.__default.SelfMut)))) {
        return (this).dtor_name;
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((this).dtor_tpe)._ToString(ind));
      }
    }
    public static RAST._IFormal self { get {
      return RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self"), RAST.__default.Self);
    } }
    public static RAST._IFormal selfOwned { get {
      return RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.Type.create_SelfOwned());
    } }
    public static RAST._IFormal selfMut { get {
      return RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut self"), RAST.__default.SelfMut);
    } }
  }

  public interface _IPattern {
    bool is_RawPattern { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
  }
  public class Pattern : _IPattern {
    public readonly Dafny.ISequence<Dafny.Rune> _i_content;
    public Pattern(Dafny.ISequence<Dafny.Rune> content) {
      this._i_content = content;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Pattern;
      return oth != null && object.Equals(this._i_content, oth._i_content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Pattern.RawPattern";
      s += "(";
      s += this._i_content.ToVerbatimString(true);
      s += ")";
      return s;
    }
    private static readonly Dafny.ISequence<Dafny.Rune> theDefault = Dafny.Sequence<Dafny.Rune>.Empty;
    public static Dafny.ISequence<Dafny.Rune> Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPattern create(Dafny.ISequence<Dafny.Rune> content) {
      return new Pattern(content);
    }
    public static _IPattern create_RawPattern(Dafny.ISequence<Dafny.Rune> content) {
      return create(content);
    }
    public bool is_RawPattern { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_content {
      get {
        return this._i_content;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> _this, Dafny.ISequence<Dafny.Rune> ind) {
      return (_this);
    }
  }

  public interface _IMatchCase {
    bool is_MatchCase { get; }
    Dafny.ISequence<Dafny.Rune> dtor_pattern { get; }
    RAST._IExpr dtor_rhs { get; }
    _IMatchCase DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class MatchCase : _IMatchCase {
    public readonly Dafny.ISequence<Dafny.Rune> _i_pattern;
    public readonly RAST._IExpr _i_rhs;
    public MatchCase(Dafny.ISequence<Dafny.Rune> pattern, RAST._IExpr rhs) {
      this._i_pattern = pattern;
      this._i_rhs = rhs;
    }
    public _IMatchCase DowncastClone() {
      if (this is _IMatchCase dt) { return dt; }
      return new MatchCase(_i_pattern, _i_rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.MatchCase;
      return oth != null && object.Equals(this._i_pattern, oth._i_pattern) && object.Equals(this._i_rhs, oth._i_rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_pattern));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.MatchCase.MatchCase";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_pattern);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_rhs);
      s += ")";
      return s;
    }
    private static readonly RAST._IMatchCase theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, RAST.Expr.Default());
    public static RAST._IMatchCase Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IMatchCase> _TYPE = new Dafny.TypeDescriptor<RAST._IMatchCase>(RAST.MatchCase.Default());
    public static Dafny.TypeDescriptor<RAST._IMatchCase> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMatchCase create(Dafny.ISequence<Dafny.Rune> pattern, RAST._IExpr rhs) {
      return new MatchCase(pattern, rhs);
    }
    public static _IMatchCase create_MatchCase(Dafny.ISequence<Dafny.Rune> pattern, RAST._IExpr rhs) {
      return create(pattern, rhs);
    }
    public bool is_MatchCase { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_pattern {
      get {
        return this._i_pattern;
      }
    }
    public RAST._IExpr dtor_rhs {
      get {
        return this._i_rhs;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      Dafny.ISequence<Dafny.Rune> _814_newIndent = ((((this).dtor_rhs).is_Block) ? (ind) : (Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)));
      Dafny.ISequence<Dafny.Rune> _815_rhsString = ((this).dtor_rhs)._ToString(_814_newIndent);
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Pattern._ToString((this).dtor_pattern, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" =>")), ((((_815_rhsString).Contains(new Dafny.Rune('\n'))) && (((_815_rhsString).Select(BigInteger.Zero)) != (new Dafny.Rune('{')))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), _815_rhsString)) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), _815_rhsString))));
    }
  }

  public interface _IAssignIdentifier {
    bool is_AssignIdentifier { get; }
    Dafny.ISequence<Dafny.Rune> dtor_identifier { get; }
    RAST._IExpr dtor_rhs { get; }
    _IAssignIdentifier DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class AssignIdentifier : _IAssignIdentifier {
    public readonly Dafny.ISequence<Dafny.Rune> _i_identifier;
    public readonly RAST._IExpr _i_rhs;
    public AssignIdentifier(Dafny.ISequence<Dafny.Rune> identifier, RAST._IExpr rhs) {
      this._i_identifier = identifier;
      this._i_rhs = rhs;
    }
    public _IAssignIdentifier DowncastClone() {
      if (this is _IAssignIdentifier dt) { return dt; }
      return new AssignIdentifier(_i_identifier, _i_rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignIdentifier;
      return oth != null && object.Equals(this._i_identifier, oth._i_identifier) && object.Equals(this._i_rhs, oth._i_rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_identifier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignIdentifier.AssignIdentifier";
      s += "(";
      s += this._i_identifier.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_rhs);
      s += ")";
      return s;
    }
    private static readonly RAST._IAssignIdentifier theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, RAST.Expr.Default());
    public static RAST._IAssignIdentifier Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IAssignIdentifier> _TYPE = new Dafny.TypeDescriptor<RAST._IAssignIdentifier>(RAST.AssignIdentifier.Default());
    public static Dafny.TypeDescriptor<RAST._IAssignIdentifier> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAssignIdentifier create(Dafny.ISequence<Dafny.Rune> identifier, RAST._IExpr rhs) {
      return new AssignIdentifier(identifier, rhs);
    }
    public static _IAssignIdentifier create_AssignIdentifier(Dafny.ISequence<Dafny.Rune> identifier, RAST._IExpr rhs) {
      return create(identifier, rhs);
    }
    public bool is_AssignIdentifier { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_identifier {
      get {
        return this._i_identifier;
      }
    }
    public RAST._IExpr dtor_rhs {
      get {
        return this._i_rhs;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_identifier, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((this).dtor_rhs)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)));
    }
  }

  public interface _IDeclareType {
    bool is_MUT { get; }
    bool is_CONST { get; }
    _IDeclareType DowncastClone();
  }
  public abstract class DeclareType : _IDeclareType {
    public DeclareType() {
    }
    private static readonly RAST._IDeclareType theDefault = create_MUT();
    public static RAST._IDeclareType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IDeclareType> _TYPE = new Dafny.TypeDescriptor<RAST._IDeclareType>(RAST.DeclareType.Default());
    public static Dafny.TypeDescriptor<RAST._IDeclareType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeclareType create_MUT() {
      return new DeclareType_MUT();
    }
    public static _IDeclareType create_CONST() {
      return new DeclareType_CONST();
    }
    public bool is_MUT { get { return this is DeclareType_MUT; } }
    public bool is_CONST { get { return this is DeclareType_CONST; } }
    public static System.Collections.Generic.IEnumerable<_IDeclareType> AllSingletonConstructors {
      get {
        yield return DeclareType.create_MUT();
        yield return DeclareType.create_CONST();
      }
    }
    public abstract _IDeclareType DowncastClone();
  }
  public class DeclareType_MUT : DeclareType {
    public DeclareType_MUT() : base() {
    }
    public override _IDeclareType DowncastClone() {
      if (this is _IDeclareType dt) { return dt; }
      return new DeclareType_MUT();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.DeclareType_MUT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.DeclareType.MUT";
      return s;
    }
  }
  public class DeclareType_CONST : DeclareType {
    public DeclareType_CONST() : base() {
    }
    public override _IDeclareType DowncastClone() {
      if (this is _IDeclareType dt) { return dt; }
      return new DeclareType_CONST();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.DeclareType_CONST;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.DeclareType.CONST";
      return s;
    }
  }

  public interface _IAssociativity {
    bool is_LeftToRight { get; }
    bool is_RightToLeft { get; }
    bool is_RequiresParentheses { get; }
    _IAssociativity DowncastClone();
  }
  public abstract class Associativity : _IAssociativity {
    public Associativity() {
    }
    private static readonly RAST._IAssociativity theDefault = create_LeftToRight();
    public static RAST._IAssociativity Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IAssociativity> _TYPE = new Dafny.TypeDescriptor<RAST._IAssociativity>(RAST.Associativity.Default());
    public static Dafny.TypeDescriptor<RAST._IAssociativity> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAssociativity create_LeftToRight() {
      return new Associativity_LeftToRight();
    }
    public static _IAssociativity create_RightToLeft() {
      return new Associativity_RightToLeft();
    }
    public static _IAssociativity create_RequiresParentheses() {
      return new Associativity_RequiresParentheses();
    }
    public bool is_LeftToRight { get { return this is Associativity_LeftToRight; } }
    public bool is_RightToLeft { get { return this is Associativity_RightToLeft; } }
    public bool is_RequiresParentheses { get { return this is Associativity_RequiresParentheses; } }
    public static System.Collections.Generic.IEnumerable<_IAssociativity> AllSingletonConstructors {
      get {
        yield return Associativity.create_LeftToRight();
        yield return Associativity.create_RightToLeft();
        yield return Associativity.create_RequiresParentheses();
      }
    }
    public abstract _IAssociativity DowncastClone();
  }
  public class Associativity_LeftToRight : Associativity {
    public Associativity_LeftToRight() : base() {
    }
    public override _IAssociativity DowncastClone() {
      if (this is _IAssociativity dt) { return dt; }
      return new Associativity_LeftToRight();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Associativity_LeftToRight;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Associativity.LeftToRight";
      return s;
    }
  }
  public class Associativity_RightToLeft : Associativity {
    public Associativity_RightToLeft() : base() {
    }
    public override _IAssociativity DowncastClone() {
      if (this is _IAssociativity dt) { return dt; }
      return new Associativity_RightToLeft();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Associativity_RightToLeft;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Associativity.RightToLeft";
      return s;
    }
  }
  public class Associativity_RequiresParentheses : Associativity {
    public Associativity_RequiresParentheses() : base() {
    }
    public override _IAssociativity DowncastClone() {
      if (this is _IAssociativity dt) { return dt; }
      return new Associativity_RequiresParentheses();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Associativity_RequiresParentheses;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Associativity.RequiresParentheses";
      return s;
    }
  }

  public interface _IPrintingInfo {
    bool is_UnknownPrecedence { get; }
    bool is_Precedence { get; }
    bool is_SuffixPrecedence { get; }
    bool is_PrecedenceAssociativity { get; }
    BigInteger dtor_precedence { get; }
    RAST._IAssociativity dtor_associativity { get; }
    _IPrintingInfo DowncastClone();
    bool NeedParenthesesFor(RAST._IPrintingInfo underlying);
    bool NeedParenthesesForLeft(RAST._IPrintingInfo underlying);
    bool NeedParenthesesForRight(RAST._IPrintingInfo underlying);
  }
  public abstract class PrintingInfo : _IPrintingInfo {
    public PrintingInfo() {
    }
    private static readonly RAST._IPrintingInfo theDefault = create_UnknownPrecedence();
    public static RAST._IPrintingInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IPrintingInfo> _TYPE = new Dafny.TypeDescriptor<RAST._IPrintingInfo>(RAST.PrintingInfo.Default());
    public static Dafny.TypeDescriptor<RAST._IPrintingInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPrintingInfo create_UnknownPrecedence() {
      return new PrintingInfo_UnknownPrecedence();
    }
    public static _IPrintingInfo create_Precedence(BigInteger precedence) {
      return new PrintingInfo_Precedence(precedence);
    }
    public static _IPrintingInfo create_SuffixPrecedence(BigInteger precedence) {
      return new PrintingInfo_SuffixPrecedence(precedence);
    }
    public static _IPrintingInfo create_PrecedenceAssociativity(BigInteger precedence, RAST._IAssociativity associativity) {
      return new PrintingInfo_PrecedenceAssociativity(precedence, associativity);
    }
    public bool is_UnknownPrecedence { get { return this is PrintingInfo_UnknownPrecedence; } }
    public bool is_Precedence { get { return this is PrintingInfo_Precedence; } }
    public bool is_SuffixPrecedence { get { return this is PrintingInfo_SuffixPrecedence; } }
    public bool is_PrecedenceAssociativity { get { return this is PrintingInfo_PrecedenceAssociativity; } }
    public BigInteger dtor_precedence {
      get {
        var d = this;
        if (d is PrintingInfo_Precedence) { return ((PrintingInfo_Precedence)d)._i_precedence; }
        if (d is PrintingInfo_SuffixPrecedence) { return ((PrintingInfo_SuffixPrecedence)d)._i_precedence; }
        return ((PrintingInfo_PrecedenceAssociativity)d)._i_precedence;
      }
    }
    public RAST._IAssociativity dtor_associativity {
      get {
        var d = this;
        return ((PrintingInfo_PrecedenceAssociativity)d)._i_associativity;
      }
    }
    public abstract _IPrintingInfo DowncastClone();
    public bool NeedParenthesesFor(RAST._IPrintingInfo underlying) {
      if ((this).is_UnknownPrecedence) {
        return true;
      } else if ((underlying).is_UnknownPrecedence) {
        return true;
      } else if (((this).dtor_precedence) <= ((underlying).dtor_precedence)) {
        return true;
      } else {
        return false;
      }
    }
    public bool NeedParenthesesForLeft(RAST._IPrintingInfo underlying) {
      if ((this).is_UnknownPrecedence) {
        return true;
      } else if ((underlying).is_UnknownPrecedence) {
        return true;
      } else if (((this).dtor_precedence) <= ((underlying).dtor_precedence)) {
        return ((((this).dtor_precedence) < ((underlying).dtor_precedence)) || (!((this).is_PrecedenceAssociativity))) || (!(((this).dtor_associativity).is_LeftToRight));
      } else {
        return false;
      }
    }
    public bool NeedParenthesesForRight(RAST._IPrintingInfo underlying) {
      if ((this).is_UnknownPrecedence) {
        return true;
      } else if ((underlying).is_UnknownPrecedence) {
        return true;
      } else if (((this).dtor_precedence) <= ((underlying).dtor_precedence)) {
        return ((((this).dtor_precedence) < ((underlying).dtor_precedence)) || (!((this).is_PrecedenceAssociativity))) || (!(((this).dtor_associativity).is_RightToLeft));
      } else {
        return false;
      }
    }
  }
  public class PrintingInfo_UnknownPrecedence : PrintingInfo {
    public PrintingInfo_UnknownPrecedence() : base() {
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_UnknownPrecedence();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_UnknownPrecedence;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.UnknownPrecedence";
      return s;
    }
  }
  public class PrintingInfo_Precedence : PrintingInfo {
    public readonly BigInteger _i_precedence;
    public PrintingInfo_Precedence(BigInteger precedence) : base() {
      this._i_precedence = precedence;
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_Precedence(_i_precedence);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_Precedence;
      return oth != null && this._i_precedence == oth._i_precedence;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_precedence));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.Precedence";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_precedence);
      s += ")";
      return s;
    }
  }
  public class PrintingInfo_SuffixPrecedence : PrintingInfo {
    public readonly BigInteger _i_precedence;
    public PrintingInfo_SuffixPrecedence(BigInteger precedence) : base() {
      this._i_precedence = precedence;
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_SuffixPrecedence(_i_precedence);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_SuffixPrecedence;
      return oth != null && this._i_precedence == oth._i_precedence;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_precedence));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.SuffixPrecedence";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_precedence);
      s += ")";
      return s;
    }
  }
  public class PrintingInfo_PrecedenceAssociativity : PrintingInfo {
    public readonly BigInteger _i_precedence;
    public readonly RAST._IAssociativity _i_associativity;
    public PrintingInfo_PrecedenceAssociativity(BigInteger precedence, RAST._IAssociativity associativity) : base() {
      this._i_precedence = precedence;
      this._i_associativity = associativity;
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_PrecedenceAssociativity(_i_precedence, _i_associativity);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_PrecedenceAssociativity;
      return oth != null && this._i_precedence == oth._i_precedence && object.Equals(this._i_associativity, oth._i_associativity);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_precedence));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_associativity));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.PrecedenceAssociativity";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_precedence);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_associativity);
      s += ")";
      return s;
    }
  }

  public interface _IExpr {
    bool is_RawExpr { get; }
    bool is_Identifier { get; }
    bool is_Match { get; }
    bool is_StmtExpr { get; }
    bool is_Block { get; }
    bool is_StructBuild { get; }
    bool is_Tuple { get; }
    bool is_UnaryOp { get; }
    bool is_BinaryOp { get; }
    bool is_TypeAscription { get; }
    bool is_LiteralInt { get; }
    bool is_LiteralString { get; }
    bool is_ConversionNum { get; }
    bool is_DeclareVar { get; }
    bool is_AssignVar { get; }
    bool is_IfExpr { get; }
    bool is_Loop { get; }
    bool is_For { get; }
    bool is_Labelled { get; }
    bool is_Break { get; }
    bool is_Continue { get; }
    bool is_Return { get; }
    bool is_Call { get; }
    bool is_Select { get; }
    bool is_MemberSelect { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IExpr dtor_matchee { get; }
    Dafny.ISequence<RAST._IMatchCase> dtor_cases { get; }
    RAST._IExpr dtor_stmt { get; }
    RAST._IExpr dtor_rhs { get; }
    RAST._IExpr dtor_underlying { get; }
    Dafny.ISequence<RAST._IAssignIdentifier> dtor_assignments { get; }
    Dafny.ISequence<RAST._IExpr> dtor_arguments { get; }
    Dafny.ISequence<Dafny.Rune> dtor_op1 { get; }
    DAST.Format._IUnaryOpFormat dtor_format { get; }
    Dafny.ISequence<Dafny.Rune> dtor_op2 { get; }
    RAST._IExpr dtor_left { get; }
    RAST._IExpr dtor_right { get; }
    DAST.Format._IBinaryOpFormat dtor_format2 { get; }
    RAST._IType dtor_tpe { get; }
    Dafny.ISequence<Dafny.Rune> dtor_value { get; }
    bool dtor_binary { get; }
    RAST._IDeclareType dtor_declareType { get; }
    Std.Wrappers._IOption<RAST._IType> dtor_optType { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_optRhs { get; }
    RAST._IExpr dtor_cond { get; }
    RAST._IExpr dtor_thn { get; }
    RAST._IExpr dtor_els { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_optCond { get; }
    RAST._IExpr dtor_range { get; }
    RAST._IExpr dtor_body { get; }
    Dafny.ISequence<Dafny.Rune> dtor_lbl { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_optLbl { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_optExpr { get; }
    RAST._IExpr dtor_obj { get; }
    Dafny.ISequence<RAST._IType> dtor_typeParameters { get; }
    _IExpr DowncastClone();
    bool NoExtraSemicolonAfter();
    RAST._IPrintingInfo printingInfo { get; }
    RAST._IExpr Optimize();
    bool LeftRequiresParentheses(RAST._IExpr left);
    _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> LeftParentheses(RAST._IExpr left);
    bool RightRequiresParentheses(RAST._IExpr right);
    _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> RightParentheses(RAST._IExpr right);
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> RightMostIdentifier();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
    RAST._IExpr Then(RAST._IExpr rhs2);
    RAST._IExpr Sel(Dafny.ISequence<Dafny.Rune> name);
    RAST._IExpr MSel(Dafny.ISequence<Dafny.Rune> name);
    RAST._IExpr Apply(Dafny.ISequence<RAST._IType> typeParameters, Dafny.ISequence<RAST._IExpr> arguments);
    RAST._IExpr Apply1(RAST._IExpr argument);
  }
  public abstract class Expr : _IExpr {
    public Expr() {
    }
    private static readonly RAST._IExpr theDefault = create_RawExpr(Dafny.Sequence<Dafny.Rune>.Empty);
    public static RAST._IExpr Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IExpr> _TYPE = new Dafny.TypeDescriptor<RAST._IExpr>(RAST.Expr.Default());
    public static Dafny.TypeDescriptor<RAST._IExpr> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExpr create_RawExpr(Dafny.ISequence<Dafny.Rune> content) {
      return new Expr_RawExpr(content);
    }
    public static _IExpr create_Identifier(Dafny.ISequence<Dafny.Rune> name) {
      return new Expr_Identifier(name);
    }
    public static _IExpr create_Match(RAST._IExpr matchee, Dafny.ISequence<RAST._IMatchCase> cases) {
      return new Expr_Match(matchee, cases);
    }
    public static _IExpr create_StmtExpr(RAST._IExpr stmt, RAST._IExpr rhs) {
      return new Expr_StmtExpr(stmt, rhs);
    }
    public static _IExpr create_Block(RAST._IExpr underlying) {
      return new Expr_Block(underlying);
    }
    public static _IExpr create_StructBuild(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IAssignIdentifier> assignments) {
      return new Expr_StructBuild(name, assignments);
    }
    public static _IExpr create_Tuple(Dafny.ISequence<RAST._IExpr> arguments) {
      return new Expr_Tuple(arguments);
    }
    public static _IExpr create_UnaryOp(Dafny.ISequence<Dafny.Rune> op1, RAST._IExpr underlying, DAST.Format._IUnaryOpFormat format) {
      return new Expr_UnaryOp(op1, underlying, format);
    }
    public static _IExpr create_BinaryOp(Dafny.ISequence<Dafny.Rune> op2, RAST._IExpr left, RAST._IExpr right, DAST.Format._IBinaryOpFormat format2) {
      return new Expr_BinaryOp(op2, left, right, format2);
    }
    public static _IExpr create_TypeAscription(RAST._IExpr left, RAST._IType tpe) {
      return new Expr_TypeAscription(left, tpe);
    }
    public static _IExpr create_LiteralInt(Dafny.ISequence<Dafny.Rune> @value) {
      return new Expr_LiteralInt(@value);
    }
    public static _IExpr create_LiteralString(Dafny.ISequence<Dafny.Rune> @value, bool binary) {
      return new Expr_LiteralString(@value, binary);
    }
    public static _IExpr create_ConversionNum(RAST._IType tpe, RAST._IExpr underlying) {
      return new Expr_ConversionNum(tpe, underlying);
    }
    public static _IExpr create_DeclareVar(RAST._IDeclareType declareType, Dafny.ISequence<Dafny.Rune> name, Std.Wrappers._IOption<RAST._IType> optType, Std.Wrappers._IOption<RAST._IExpr> optRhs) {
      return new Expr_DeclareVar(declareType, name, optType, optRhs);
    }
    public static _IExpr create_AssignVar(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr rhs) {
      return new Expr_AssignVar(name, rhs);
    }
    public static _IExpr create_IfExpr(RAST._IExpr cond, RAST._IExpr thn, RAST._IExpr els) {
      return new Expr_IfExpr(cond, thn, els);
    }
    public static _IExpr create_Loop(Std.Wrappers._IOption<RAST._IExpr> optCond, RAST._IExpr underlying) {
      return new Expr_Loop(optCond, underlying);
    }
    public static _IExpr create_For(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr range, RAST._IExpr body) {
      return new Expr_For(name, range, body);
    }
    public static _IExpr create_Labelled(Dafny.ISequence<Dafny.Rune> lbl, RAST._IExpr underlying) {
      return new Expr_Labelled(lbl, underlying);
    }
    public static _IExpr create_Break(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) {
      return new Expr_Break(optLbl);
    }
    public static _IExpr create_Continue(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) {
      return new Expr_Continue(optLbl);
    }
    public static _IExpr create_Return(Std.Wrappers._IOption<RAST._IExpr> optExpr) {
      return new Expr_Return(optExpr);
    }
    public static _IExpr create_Call(RAST._IExpr obj, Dafny.ISequence<RAST._IType> typeParameters, Dafny.ISequence<RAST._IExpr> arguments) {
      return new Expr_Call(obj, typeParameters, arguments);
    }
    public static _IExpr create_Select(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) {
      return new Expr_Select(obj, name);
    }
    public static _IExpr create_MemberSelect(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) {
      return new Expr_MemberSelect(obj, name);
    }
    public bool is_RawExpr { get { return this is Expr_RawExpr; } }
    public bool is_Identifier { get { return this is Expr_Identifier; } }
    public bool is_Match { get { return this is Expr_Match; } }
    public bool is_StmtExpr { get { return this is Expr_StmtExpr; } }
    public bool is_Block { get { return this is Expr_Block; } }
    public bool is_StructBuild { get { return this is Expr_StructBuild; } }
    public bool is_Tuple { get { return this is Expr_Tuple; } }
    public bool is_UnaryOp { get { return this is Expr_UnaryOp; } }
    public bool is_BinaryOp { get { return this is Expr_BinaryOp; } }
    public bool is_TypeAscription { get { return this is Expr_TypeAscription; } }
    public bool is_LiteralInt { get { return this is Expr_LiteralInt; } }
    public bool is_LiteralString { get { return this is Expr_LiteralString; } }
    public bool is_ConversionNum { get { return this is Expr_ConversionNum; } }
    public bool is_DeclareVar { get { return this is Expr_DeclareVar; } }
    public bool is_AssignVar { get { return this is Expr_AssignVar; } }
    public bool is_IfExpr { get { return this is Expr_IfExpr; } }
    public bool is_Loop { get { return this is Expr_Loop; } }
    public bool is_For { get { return this is Expr_For; } }
    public bool is_Labelled { get { return this is Expr_Labelled; } }
    public bool is_Break { get { return this is Expr_Break; } }
    public bool is_Continue { get { return this is Expr_Continue; } }
    public bool is_Return { get { return this is Expr_Return; } }
    public bool is_Call { get { return this is Expr_Call; } }
    public bool is_Select { get { return this is Expr_Select; } }
    public bool is_MemberSelect { get { return this is Expr_MemberSelect; } }
    public Dafny.ISequence<Dafny.Rune> dtor_content {
      get {
        var d = this;
        return ((Expr_RawExpr)d)._i_content;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Expr_Identifier) { return ((Expr_Identifier)d)._i_name; }
        if (d is Expr_StructBuild) { return ((Expr_StructBuild)d)._i_name; }
        if (d is Expr_DeclareVar) { return ((Expr_DeclareVar)d)._i_name; }
        if (d is Expr_AssignVar) { return ((Expr_AssignVar)d)._i_name; }
        if (d is Expr_For) { return ((Expr_For)d)._i_name; }
        if (d is Expr_Select) { return ((Expr_Select)d)._i_name; }
        return ((Expr_MemberSelect)d)._i_name;
      }
    }
    public RAST._IExpr dtor_matchee {
      get {
        var d = this;
        return ((Expr_Match)d)._i_matchee;
      }
    }
    public Dafny.ISequence<RAST._IMatchCase> dtor_cases {
      get {
        var d = this;
        return ((Expr_Match)d)._i_cases;
      }
    }
    public RAST._IExpr dtor_stmt {
      get {
        var d = this;
        return ((Expr_StmtExpr)d)._i_stmt;
      }
    }
    public RAST._IExpr dtor_rhs {
      get {
        var d = this;
        if (d is Expr_StmtExpr) { return ((Expr_StmtExpr)d)._i_rhs; }
        return ((Expr_AssignVar)d)._i_rhs;
      }
    }
    public RAST._IExpr dtor_underlying {
      get {
        var d = this;
        if (d is Expr_Block) { return ((Expr_Block)d)._i_underlying; }
        if (d is Expr_UnaryOp) { return ((Expr_UnaryOp)d)._i_underlying; }
        if (d is Expr_ConversionNum) { return ((Expr_ConversionNum)d)._i_underlying; }
        if (d is Expr_Loop) { return ((Expr_Loop)d)._i_underlying; }
        return ((Expr_Labelled)d)._i_underlying;
      }
    }
    public Dafny.ISequence<RAST._IAssignIdentifier> dtor_assignments {
      get {
        var d = this;
        return ((Expr_StructBuild)d)._i_assignments;
      }
    }
    public Dafny.ISequence<RAST._IExpr> dtor_arguments {
      get {
        var d = this;
        if (d is Expr_Tuple) { return ((Expr_Tuple)d)._i_arguments; }
        return ((Expr_Call)d)._i_arguments;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_op1 {
      get {
        var d = this;
        return ((Expr_UnaryOp)d)._i_op1;
      }
    }
    public DAST.Format._IUnaryOpFormat dtor_format {
      get {
        var d = this;
        return ((Expr_UnaryOp)d)._i_format;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_op2 {
      get {
        var d = this;
        return ((Expr_BinaryOp)d)._i_op2;
      }
    }
    public RAST._IExpr dtor_left {
      get {
        var d = this;
        if (d is Expr_BinaryOp) { return ((Expr_BinaryOp)d)._i_left; }
        return ((Expr_TypeAscription)d)._i_left;
      }
    }
    public RAST._IExpr dtor_right {
      get {
        var d = this;
        return ((Expr_BinaryOp)d)._i_right;
      }
    }
    public DAST.Format._IBinaryOpFormat dtor_format2 {
      get {
        var d = this;
        return ((Expr_BinaryOp)d)._i_format2;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        var d = this;
        if (d is Expr_TypeAscription) { return ((Expr_TypeAscription)d)._i_tpe; }
        return ((Expr_ConversionNum)d)._i_tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_value {
      get {
        var d = this;
        if (d is Expr_LiteralInt) { return ((Expr_LiteralInt)d)._i_value; }
        return ((Expr_LiteralString)d)._i_value;
      }
    }
    public bool dtor_binary {
      get {
        var d = this;
        return ((Expr_LiteralString)d)._i_binary;
      }
    }
    public RAST._IDeclareType dtor_declareType {
      get {
        var d = this;
        return ((Expr_DeclareVar)d)._i_declareType;
      }
    }
    public Std.Wrappers._IOption<RAST._IType> dtor_optType {
      get {
        var d = this;
        return ((Expr_DeclareVar)d)._i_optType;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_optRhs {
      get {
        var d = this;
        return ((Expr_DeclareVar)d)._i_optRhs;
      }
    }
    public RAST._IExpr dtor_cond {
      get {
        var d = this;
        return ((Expr_IfExpr)d)._i_cond;
      }
    }
    public RAST._IExpr dtor_thn {
      get {
        var d = this;
        return ((Expr_IfExpr)d)._i_thn;
      }
    }
    public RAST._IExpr dtor_els {
      get {
        var d = this;
        return ((Expr_IfExpr)d)._i_els;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_optCond {
      get {
        var d = this;
        return ((Expr_Loop)d)._i_optCond;
      }
    }
    public RAST._IExpr dtor_range {
      get {
        var d = this;
        return ((Expr_For)d)._i_range;
      }
    }
    public RAST._IExpr dtor_body {
      get {
        var d = this;
        return ((Expr_For)d)._i_body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_lbl {
      get {
        var d = this;
        return ((Expr_Labelled)d)._i_lbl;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_optLbl {
      get {
        var d = this;
        if (d is Expr_Break) { return ((Expr_Break)d)._i_optLbl; }
        return ((Expr_Continue)d)._i_optLbl;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_optExpr {
      get {
        var d = this;
        return ((Expr_Return)d)._i_optExpr;
      }
    }
    public RAST._IExpr dtor_obj {
      get {
        var d = this;
        if (d is Expr_Call) { return ((Expr_Call)d)._i_obj; }
        if (d is Expr_Select) { return ((Expr_Select)d)._i_obj; }
        return ((Expr_MemberSelect)d)._i_obj;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_typeParameters {
      get {
        var d = this;
        return ((Expr_Call)d)._i_typeParameters;
      }
    }
    public abstract _IExpr DowncastClone();
    public bool NoExtraSemicolonAfter() {
      return ((((((this).is_DeclareVar) || ((this).is_AssignVar)) || ((this).is_Break)) || ((this).is_Continue)) || ((this).is_Return)) || ((((this).is_RawExpr) && ((new BigInteger(((this).dtor_content).Count)).Sign == 1)) && ((((this).dtor_content).Select((new BigInteger(((this).dtor_content).Count)) - (BigInteger.One))) == (new Dafny.Rune(';'))));
    }
    public RAST._IExpr Optimize() {
      RAST._IExpr _source27 = this;
      bool unmatched27 = true;
      if (unmatched27) {
        if (_source27.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> op10 = _source27.dtor_op1;
          if (op10 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) {
            RAST._IExpr underlying0 = _source27.dtor_underlying;
            if (underlying0.is_Call) {
              RAST._IExpr obj0 = underlying0.dtor_obj;
              if (obj0.is_Select) {
                RAST._IExpr _816_underlying = obj0.dtor_obj;
                Dafny.ISequence<Dafny.Rune> name0 = obj0.dtor_name;
                if (name0 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone")) {
                  Dafny.ISequence<RAST._IType> _817_typeArgs = underlying0.dtor_typeParameters;
                  Dafny.ISequence<RAST._IExpr> _818_args = underlying0.dtor_arguments;
                  DAST.Format._IUnaryOpFormat _819_format = _source27.dtor_format;
                  unmatched27 = false;
                  if (((_817_typeArgs).Equals(Dafny.Sequence<RAST._IType>.FromElements())) && ((_818_args).Equals(Dafny.Sequence<RAST._IExpr>.FromElements()))) {
                    return RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _816_underlying, _819_format);
                  } else {
                    return this;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched27) {
        if (_source27.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> op11 = _source27.dtor_op1;
          if (op11 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!")) {
            RAST._IExpr underlying1 = _source27.dtor_underlying;
            if (underlying1.is_BinaryOp) {
              Dafny.ISequence<Dafny.Rune> op20 = underlying1.dtor_op2;
              if (op20 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("==")) {
                RAST._IExpr _820_left = underlying1.dtor_left;
                RAST._IExpr _821_right = underlying1.dtor_right;
                DAST.Format._IBinaryOpFormat _822_format = underlying1.dtor_format2;
                DAST.Format._IUnaryOpFormat format0 = _source27.dtor_format;
                if (format0.is_CombineFormat) {
                  unmatched27 = false;
                  return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="), _820_left, _821_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            }
          }
        }
      }
      if (unmatched27) {
        if (_source27.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> op12 = _source27.dtor_op1;
          if (op12 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!")) {
            RAST._IExpr underlying2 = _source27.dtor_underlying;
            if (underlying2.is_BinaryOp) {
              Dafny.ISequence<Dafny.Rune> op21 = underlying2.dtor_op2;
              if (op21 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")) {
                RAST._IExpr _823_left = underlying2.dtor_left;
                RAST._IExpr _824_right = underlying2.dtor_right;
                DAST.Format._IBinaryOpFormat format20 = underlying2.dtor_format2;
                if (format20.is_NoFormat) {
                  DAST.Format._IUnaryOpFormat format1 = _source27.dtor_format;
                  if (format1.is_CombineFormat) {
                    unmatched27 = false;
                    return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="), _823_left, _824_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched27) {
        if (_source27.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> op13 = _source27.dtor_op1;
          if (op13 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!")) {
            RAST._IExpr underlying3 = _source27.dtor_underlying;
            if (underlying3.is_BinaryOp) {
              Dafny.ISequence<Dafny.Rune> op22 = underlying3.dtor_op2;
              if (op22 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")) {
                RAST._IExpr _825_left = underlying3.dtor_left;
                RAST._IExpr _826_right = underlying3.dtor_right;
                DAST.Format._IBinaryOpFormat format21 = underlying3.dtor_format2;
                if (format21.is_ReverseFormat) {
                  DAST.Format._IUnaryOpFormat format2 = _source27.dtor_format;
                  if (format2.is_CombineFormat) {
                    unmatched27 = false;
                    return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _826_right, _825_left, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched27) {
        if (_source27.is_ConversionNum) {
          RAST._IType _827_tpe = _source27.dtor_tpe;
          RAST._IExpr _828_expr = _source27.dtor_underlying;
          unmatched27 = false;
          if (((((((((((_827_tpe).is_U8) || ((_827_tpe).is_U16)) || ((_827_tpe).is_U32)) || ((_827_tpe).is_U64)) || ((_827_tpe).is_U128)) || ((_827_tpe).is_I8)) || ((_827_tpe).is_I16)) || ((_827_tpe).is_I32)) || ((_827_tpe).is_I64)) || ((_827_tpe).is_I128)) {
            RAST._IExpr _source28 = _828_expr;
            bool unmatched28 = true;
            if (unmatched28) {
              if (_source28.is_Call) {
                RAST._IExpr obj1 = _source28.dtor_obj;
                if (obj1.is_MemberSelect) {
                  RAST._IExpr obj2 = obj1.dtor_obj;
                  if (obj2.is_MemberSelect) {
                    RAST._IExpr obj3 = obj2.dtor_obj;
                    if (obj3.is_MemberSelect) {
                      RAST._IExpr obj4 = obj3.dtor_obj;
                      if (obj4.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name1 = obj4.dtor_name;
                        if (name1 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) {
                          Dafny.ISequence<Dafny.Rune> name2 = obj3.dtor_name;
                          if (name2 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime")) {
                            Dafny.ISequence<Dafny.Rune> name3 = obj2.dtor_name;
                            if (name3 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt")) {
                              Dafny.ISequence<Dafny.Rune> name4 = obj1.dtor_name;
                              if (name4 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from")) {
                                Dafny.ISequence<RAST._IType> _829_tpe = _source28.dtor_typeParameters;
                                Dafny.ISequence<RAST._IExpr> _830_args = _source28.dtor_arguments;
                                unmatched28 = false;
                                if (((new BigInteger((_829_tpe).Count)).Sign == 0) && ((new BigInteger((_830_args).Count)) == (BigInteger.One))) {
                                  RAST._IExpr _source29 = (_830_args).Select(BigInteger.Zero);
                                  bool unmatched29 = true;
                                  if (unmatched29) {
                                    if (_source29.is_LiteralInt) {
                                      Dafny.ISequence<Dafny.Rune> _831_number = _source29.dtor_value;
                                      unmatched29 = false;
                                      return RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/*optimized*/"), _831_number));
                                    }
                                  }
                                  if (unmatched29) {
                                    if (_source29.is_LiteralString) {
                                      Dafny.ISequence<Dafny.Rune> _832_number = _source29.dtor_value;
                                      bool _833___v22 = _source29.dtor_binary;
                                      unmatched29 = false;
                                      return RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/*optimized*/"), _832_number));
                                    }
                                  }
                                  if (unmatched29) {
                                    RAST._IExpr _834___v23 = _source29;
                                    unmatched29 = false;
                                    return this;
                                  }
                                  throw new System.Exception("unexpected control point");
                                } else {
                                  return this;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            if (unmatched28) {
              RAST._IExpr _835___v24 = _source28;
              unmatched28 = false;
              return this;
            }
            throw new System.Exception("unexpected control point");
          } else {
            return this;
          }
        }
      }
      if (unmatched27) {
        if (_source27.is_StmtExpr) {
          RAST._IExpr stmt0 = _source27.dtor_stmt;
          if (stmt0.is_DeclareVar) {
            RAST._IDeclareType _836_mod = stmt0.dtor_declareType;
            Dafny.ISequence<Dafny.Rune> _837_name = stmt0.dtor_name;
            Std.Wrappers._IOption<RAST._IType> optType0 = stmt0.dtor_optType;
            if (optType0.is_Some) {
              RAST._IType _838_tpe = optType0.dtor_value;
              Std.Wrappers._IOption<RAST._IExpr> optRhs0 = stmt0.dtor_optRhs;
              if (optRhs0.is_None) {
                RAST._IExpr rhs0 = _source27.dtor_rhs;
                if (rhs0.is_StmtExpr) {
                  RAST._IExpr stmt1 = rhs0.dtor_stmt;
                  if (stmt1.is_AssignVar) {
                    Dafny.ISequence<Dafny.Rune> _839_name2 = stmt1.dtor_name;
                    RAST._IExpr _840_rhs = stmt1.dtor_rhs;
                    RAST._IExpr _841_last = rhs0.dtor_rhs;
                    unmatched27 = false;
                    if ((_837_name).Equals(_839_name2)) {
                      RAST._IExpr _842_rewriting = RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(_836_mod, _837_name, Std.Wrappers.Option<RAST._IType>.create_Some(_838_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_840_rhs)), _841_last);
                      return _842_rewriting;
                    } else {
                      return this;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched27) {
        RAST._IExpr _843___v25 = _source27;
        unmatched27 = false;
        return this;
      }
      throw new System.Exception("unexpected control point");
    }
    public bool LeftRequiresParentheses(RAST._IExpr left) {
      return ((this).printingInfo).NeedParenthesesForLeft((left).printingInfo);
    }
    public _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> LeftParentheses(RAST._IExpr left) {
      if ((this).LeftRequiresParentheses(left)) {
        return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else {
        return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      }
    }
    public bool RightRequiresParentheses(RAST._IExpr right) {
      return ((this).printingInfo).NeedParenthesesForRight((right).printingInfo);
    }
    public _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> RightParentheses(RAST._IExpr right) {
      if ((this).RightRequiresParentheses(right)) {
        return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else {
        return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> RightMostIdentifier() {
      RAST._IExpr _source30 = this;
      bool unmatched30 = true;
      if (unmatched30) {
        if (_source30.is_MemberSelect) {
          RAST._IExpr _844___v26 = _source30.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _845_id = _source30.dtor_name;
          unmatched30 = false;
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_845_id);
        }
      }
      if (unmatched30) {
        RAST._IExpr _846___v27 = _source30;
        unmatched30 = false;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      }
      throw new System.Exception("unexpected control point");
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      var _pat_let_tv39 = ind;
      var _pat_let_tv40 = ind;
      var _pat_let_tv41 = ind;
      var _pat_let_tv42 = ind;
      var _pat_let_tv43 = ind;
      var _pat_let_tv44 = ind;
      var _pat_let_tv45 = ind;
      var _pat_let_tv46 = ind;
      var _pat_let_tv47 = ind;
      var _pat_let_tv48 = ind;
      var _pat_let_tv49 = ind;
      var _pat_let_tv50 = ind;
      var _pat_let_tv51 = ind;
      var _pat_let_tv52 = ind;
      var _pat_let_tv53 = ind;
      var _pat_let_tv54 = ind;
      var _pat_let_tv55 = ind;
      var _pat_let_tv56 = ind;
      var _pat_let_tv57 = ind;
      var _pat_let_tv58 = ind;
      var _pat_let_tv59 = ind;
      var _pat_let_tv60 = ind;
      var _pat_let_tv61 = ind;
      var _pat_let_tv62 = ind;
      var _pat_let_tv63 = ind;
      var _pat_let_tv64 = ind;
      var _pat_let_tv65 = ind;
      var _pat_let_tv66 = ind;
      var _pat_let_tv67 = ind;
      var _pat_let_tv68 = ind;
      var _pat_let_tv69 = ind;
      var _pat_let_tv70 = ind;
      var _pat_let_tv71 = ind;
      var _pat_let_tv72 = ind;
      var _pat_let_tv73 = ind;
      var _pat_let_tv74 = ind;
      var _pat_let_tv75 = ind;
      var _pat_let_tv76 = ind;
      var _pat_let_tv77 = ind;
      var _pat_let_tv78 = ind;
      var _pat_let_tv79 = ind;
      var _pat_let_tv80 = ind;
      var _pat_let_tv81 = ind;
      var _pat_let_tv82 = ind;
      var _pat_let_tv83 = ind;
      var _pat_let_tv84 = ind;
      var _pat_let_tv85 = ind;
      var _pat_let_tv86 = ind;
      RAST._IExpr _source31 = (this).Optimize();
      bool unmatched31 = true;
      if (unmatched31) {
        if (_source31.is_Identifier) {
          Dafny.ISequence<Dafny.Rune> _847_name = _source31.dtor_name;
          unmatched31 = false;
          return _847_name;
        }
      }
      if (unmatched31) {
        if (_source31.is_LiteralInt) {
          Dafny.ISequence<Dafny.Rune> _848_number = _source31.dtor_value;
          unmatched31 = false;
          return _848_number;
        }
      }
      if (unmatched31) {
        if (_source31.is_LiteralString) {
          Dafny.ISequence<Dafny.Rune> _849_characters = _source31.dtor_value;
          bool _850_binary = _source31.dtor_binary;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((_850_binary) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("b")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\"")), _849_characters), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""));
        }
      }
      if (unmatched31) {
        if (_source31.is_ConversionNum) {
          RAST._IType _851_tpe = _source31.dtor_tpe;
          RAST._IExpr _852_expr = _source31.dtor_underlying;
          unmatched31 = false;
          if (((((((((((_851_tpe).is_U8) || ((_851_tpe).is_U16)) || ((_851_tpe).is_U32)) || ((_851_tpe).is_U64)) || ((_851_tpe).is_U128)) || ((_851_tpe).is_I8)) || ((_851_tpe).is_I16)) || ((_851_tpe).is_I32)) || ((_851_tpe).is_I64)) || ((_851_tpe).is_I128)) {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("num::ToPrimitive::to_"), (_851_tpe)._ToString(_pat_let_tv39)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_852_expr)._ToString(_pat_let_tv40)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<b>Unsupported: Numeric conversion to "), (_851_tpe)._ToString(_pat_let_tv41)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</b>"));
          }
        }
      }
      if (unmatched31) {
        if (_source31.is_Match) {
          RAST._IExpr _853_matchee = _source31.dtor_matchee;
          Dafny.ISequence<RAST._IMatchCase> _854_cases = _source31.dtor_cases;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match "), (_853_matchee)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv42, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IMatchCase>(_854_cases, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IMatchCase, Dafny.ISequence<Dafny.Rune>>>>((_855_ind) => ((System.Func<RAST._IMatchCase, Dafny.ISequence<Dafny.Rune>>)((_856_c) => {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _855_ind), RAST.__default.IND), (_856_c)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_855_ind, RAST.__default.IND)));
          })))(_pat_let_tv43), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv44), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched31) {
        if (_source31.is_StmtExpr) {
          RAST._IExpr _857_stmt = _source31.dtor_stmt;
          RAST._IExpr _858_rhs = _source31.dtor_rhs;
          unmatched31 = false;
          if (((_857_stmt).is_RawExpr) && (((_857_stmt).dtor_content).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
            return (_858_rhs)._ToString(_pat_let_tv45);
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_857_stmt)._ToString(_pat_let_tv46), (((_857_stmt).NoExtraSemicolonAfter()) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv47), (_858_rhs)._ToString(_pat_let_tv48));
          }
        }
      }
      if (unmatched31) {
        if (_source31.is_Block) {
          RAST._IExpr _859_underlying = _source31.dtor_underlying;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n"), _pat_let_tv49), RAST.__default.IND), (_859_underlying)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv50, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv51), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched31) {
        if (_source31.is_IfExpr) {
          RAST._IExpr _860_cond = _source31.dtor_cond;
          RAST._IExpr _861_thn = _source31.dtor_thn;
          RAST._IExpr _862_els = _source31.dtor_els;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), (_860_cond)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv52, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _pat_let_tv53), RAST.__default.IND), (_861_thn)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv54, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv55), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} else {\n")), _pat_let_tv56), RAST.__default.IND), (_862_els)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv57, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv58), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched31) {
        if (_source31.is_StructBuild) {
          Dafny.ISequence<Dafny.Rune> _863_name = _source31.dtor_name;
          Dafny.ISequence<RAST._IAssignIdentifier> _864_assignments = _source31.dtor_assignments;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_863_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IAssignIdentifier>(_864_assignments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>>>((_865_ind) => ((System.Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>)((_866_assignment) => {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _865_ind), RAST.__default.IND), (_866_assignment)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_865_ind, RAST.__default.IND)));
          })))(_pat_let_tv59), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_864_assignments).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _pat_let_tv60)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched31) {
        if (_source31.is_Tuple) {
          Dafny.ISequence<RAST._IExpr> _867_arguments = _source31.dtor_arguments;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._IExpr>(_867_arguments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_868_ind) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_869_arg) => {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _868_ind), RAST.__default.IND), (_869_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_868_ind, RAST.__default.IND)));
          })))(_pat_let_tv61), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_867_arguments).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _pat_let_tv62)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      }
      if (unmatched31) {
        if (_source31.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> _870_op = _source31.dtor_op1;
          RAST._IExpr _871_underlying = _source31.dtor_underlying;
          DAST.Format._IUnaryOpFormat _872_format = _source31.dtor_format;
          unmatched31 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs41 = ((((this).printingInfo).NeedParenthesesFor((_871_underlying).printingInfo)) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))) : (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
          Dafny.ISequence<Dafny.Rune> _873_leftP = _let_tmp_rhs41.dtor__0;
          Dafny.ISequence<Dafny.Rune> _874_rightP = _let_tmp_rhs41.dtor__1;
          Dafny.ISequence<Dafny.Rune> _875_leftOp = ((((_870_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"))) && (!(_873_leftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_870_op, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))) : ((((_870_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (_870_op))));
          Dafny.ISequence<Dafny.Rune> _876_rightOp = (((_870_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) ? (_870_op) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_875_leftOp, _873_leftP), (_871_underlying)._ToString(_pat_let_tv63)), _874_rightP), _876_rightOp);
        }
      }
      if (unmatched31) {
        if (_source31.is_TypeAscription) {
          RAST._IExpr _877_left = _source31.dtor_left;
          RAST._IType _878_tpe = _source31.dtor_tpe;
          unmatched31 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs42 = (this).LeftParentheses(_877_left);
          Dafny.ISequence<Dafny.Rune> _879_leftLeftP = _let_tmp_rhs42.dtor__0;
          Dafny.ISequence<Dafny.Rune> _880_leftRightP = _let_tmp_rhs42.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_879_leftLeftP, (_877_left)._ToString(RAST.__default.IND)), _880_leftRightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ")), (_878_tpe)._ToString(RAST.__default.IND));
        }
      }
      if (unmatched31) {
        if (_source31.is_BinaryOp) {
          Dafny.ISequence<Dafny.Rune> _881_op2 = _source31.dtor_op2;
          RAST._IExpr _882_left = _source31.dtor_left;
          RAST._IExpr _883_right = _source31.dtor_right;
          DAST.Format._IBinaryOpFormat _884_format = _source31.dtor_format2;
          unmatched31 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs43 = (this).LeftParentheses(_882_left);
          Dafny.ISequence<Dafny.Rune> _885_leftLeftP = _let_tmp_rhs43.dtor__0;
          Dafny.ISequence<Dafny.Rune> _886_leftRighP = _let_tmp_rhs43.dtor__1;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs44 = (this).RightParentheses(_883_right);
          Dafny.ISequence<Dafny.Rune> _887_rightLeftP = _let_tmp_rhs44.dtor__0;
          Dafny.ISequence<Dafny.Rune> _888_rightRightP = _let_tmp_rhs44.dtor__1;
          Dafny.ISequence<Dafny.Rune> _889_opRendered = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), _881_op2), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
          Dafny.ISequence<Dafny.Rune> _890_indLeft = (((_885_leftLeftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv64, RAST.__default.IND)) : (_pat_let_tv65));
          Dafny.ISequence<Dafny.Rune> _891_indRight = (((_887_rightLeftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv66, RAST.__default.IND)) : (_pat_let_tv67));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_885_leftLeftP, (_882_left)._ToString(_890_indLeft)), _886_leftRighP), _889_opRendered), _887_rightLeftP), (_883_right)._ToString(_891_indRight)), _888_rightRightP);
        }
      }
      if (unmatched31) {
        if (_source31.is_DeclareVar) {
          RAST._IDeclareType _892_declareType = _source31.dtor_declareType;
          Dafny.ISequence<Dafny.Rune> _893_name = _source31.dtor_name;
          Std.Wrappers._IOption<RAST._IType> _894_optType = _source31.dtor_optType;
          Std.Wrappers._IOption<RAST._IExpr> _895_optExpr = _source31.dtor_optRhs;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let "), ((object.Equals(_892_declareType, RAST.DeclareType.create_MUT())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut ")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _893_name), (((_894_optType).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), ((_894_optType).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv68, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), (((_895_optExpr).is_Some) ? (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((_895_optExpr).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv69, RAST.__default.IND)), _pat_let5_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let5_0, _896_optExprString => (((_896_optExprString).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("= /*issue with empty RHS*/"), ((((_895_optExpr).dtor_value).is_RawExpr) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty Raw expr")) : (((((_895_optExpr).dtor_value).is_LiteralString) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty string literal")) : (((((_895_optExpr).dtor_value).is_LiteralInt) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty int literal")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Another case"))))))))) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "), _896_optExprString)))))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      if (unmatched31) {
        if (_source31.is_AssignVar) {
          Dafny.ISequence<Dafny.Rune> _897_name = _source31.dtor_name;
          RAST._IExpr _898_expr = _source31.dtor_rhs;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_897_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (_898_expr)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv70, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      if (unmatched31) {
        if (_source31.is_Labelled) {
          Dafny.ISequence<Dafny.Rune> _899_name = _source31.dtor_lbl;
          RAST._IExpr _900_underlying = _source31.dtor_underlying;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"), _899_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_900_underlying)._ToString(_pat_let_tv71));
        }
      }
      if (unmatched31) {
        if (_source31.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _901_optLbl = _source31.dtor_optLbl;
          unmatched31 = false;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source32 = _901_optLbl;
          bool unmatched32 = true;
          if (unmatched32) {
            if (_source32.is_Some) {
              Dafny.ISequence<Dafny.Rune> _902_lbl = _source32.dtor_value;
              unmatched32 = false;
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break '"), _902_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          }
          if (unmatched32) {
            unmatched32 = false;
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;");
          }
          throw new System.Exception("unexpected control point");
        }
      }
      if (unmatched31) {
        if (_source31.is_Continue) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _903_optLbl = _source31.dtor_optLbl;
          unmatched31 = false;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source33 = _903_optLbl;
          bool unmatched33 = true;
          if (unmatched33) {
            if (_source33.is_Some) {
              Dafny.ISequence<Dafny.Rune> _904_lbl = _source33.dtor_value;
              unmatched33 = false;
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue '"), _904_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          }
          if (unmatched33) {
            unmatched33 = false;
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue;");
          }
          throw new System.Exception("unexpected control point");
        }
      }
      if (unmatched31) {
        if (_source31.is_Loop) {
          Std.Wrappers._IOption<RAST._IExpr> _905_optCond = _source31.dtor_optCond;
          RAST._IExpr _906_underlying = _source31.dtor_underlying;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((System.Func<Std.Wrappers._IOption<RAST._IExpr>, Dafny.ISequence<Dafny.Rune>>)((_source34) => {
            bool unmatched34 = true;
            if (unmatched34) {
              if (_source34.is_None) {
                unmatched34 = false;
                return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop");
              }
            }
            if (unmatched34) {
              RAST._IExpr _907_c = _source34.dtor_value;
              unmatched34 = false;
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), (_907_c)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv72, RAST.__default.IND)));
            }
            throw new System.Exception("unexpected control point");
          }))(_905_optCond), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _pat_let_tv73), RAST.__default.IND), (_906_underlying)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv74, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv75), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched31) {
        if (_source31.is_For) {
          Dafny.ISequence<Dafny.Rune> _908_name = _source31.dtor_name;
          RAST._IExpr _909_range = _source31.dtor_range;
          RAST._IExpr _910_body = _source31.dtor_body;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for "), _908_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" in ")), (_909_range)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv76, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _pat_let_tv77), RAST.__default.IND), (_910_body)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv78, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv79), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched31) {
        if (_source31.is_Return) {
          Std.Wrappers._IOption<RAST._IExpr> _911_optExpr = _source31.dtor_optExpr;
          unmatched31 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), (((_911_optExpr).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), ((_911_optExpr).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv80, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      if (unmatched31) {
        if (_source31.is_Call) {
          RAST._IExpr _912_expr = _source31.dtor_obj;
          Dafny.ISequence<RAST._IType> _913_tpes = _source31.dtor_typeParameters;
          Dafny.ISequence<RAST._IExpr> _914_args = _source31.dtor_arguments;
          unmatched31 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs45 = (this).LeftParentheses(_912_expr);
          Dafny.ISequence<Dafny.Rune> _915_leftP = _let_tmp_rhs45.dtor__0;
          Dafny.ISequence<Dafny.Rune> _916_rightP = _let_tmp_rhs45.dtor__1;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs46 = ((System.Func<Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>>, _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>)((_source35) => {
            bool unmatched35 = true;
            if (unmatched35) {
              if (_source35.is_Some) {
                Dafny.ISequence<Dafny.Rune> value0 = _source35.dtor_value;
                if (value0 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!")) {
                  if (_source35.is_Some) {
                    Dafny.ISequence<Dafny.Rune> value1 = _source35.dtor_value;
                    if (value1 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!")) {
                      unmatched35 = false;
                      return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("["), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
                    }
                  }
                }
              }
            }
            if (unmatched35) {
              if (_source35.is_Some) {
                Dafny.ISequence<Dafny.Rune> value2 = _source35.dtor_value;
                if (value2 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!")) {
                  if (_source35.is_Some) {
                    Dafny.ISequence<Dafny.Rune> value3 = _source35.dtor_value;
                    if (value3 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!")) {
                      unmatched35 = false;
                      return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
                    }
                  }
                }
              }
            }
            if (unmatched35) {
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _917___v28 = _source35;
              unmatched35 = false;
              return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            throw new System.Exception("unexpected control point");
          }))((_912_expr).RightMostIdentifier());
          Dafny.ISequence<Dafny.Rune> _918_leftCallP = _let_tmp_rhs46.dtor__0;
          Dafny.ISequence<Dafny.Rune> _919_rightCallP = _let_tmp_rhs46.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_915_leftP, (_912_expr)._ToString(_pat_let_tv81)), _916_rightP), (((new BigInteger((_913_tpes).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<"), RAST.__default.SeqToString<RAST._IType>(_913_tpes, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_920_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_921_tpe) => {
            return (_921_tpe)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_920_ind, RAST.__default.IND));
          })))(_pat_let_tv82), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))))), _918_leftCallP), RAST.__default.SeqToString<RAST._IExpr>(_914_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_922_ind) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_923_arg) => {
            return (_923_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_922_ind, RAST.__default.IND));
          })))(_pat_let_tv83), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), _919_rightCallP);
        }
      }
      if (unmatched31) {
        if (_source31.is_Select) {
          RAST._IExpr _924_expression = _source31.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _925_name = _source31.dtor_name;
          unmatched31 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs47 = (this).LeftParentheses(_924_expression);
          Dafny.ISequence<Dafny.Rune> _926_leftP = _let_tmp_rhs47.dtor__0;
          Dafny.ISequence<Dafny.Rune> _927_rightP = _let_tmp_rhs47.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_926_leftP, (_924_expression)._ToString(_pat_let_tv84)), _927_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _925_name);
        }
      }
      if (unmatched31) {
        if (_source31.is_MemberSelect) {
          RAST._IExpr _928_expression = _source31.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _929_name = _source31.dtor_name;
          unmatched31 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs48 = (this).LeftParentheses(_928_expression);
          Dafny.ISequence<Dafny.Rune> _930_leftP = _let_tmp_rhs48.dtor__0;
          Dafny.ISequence<Dafny.Rune> _931_rightP = _let_tmp_rhs48.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_930_leftP, (_928_expression)._ToString(_pat_let_tv85)), _931_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _929_name);
        }
      }
      if (unmatched31) {
        RAST._IExpr _932_r = _source31;
        unmatched31 = false;
        return RAST.__default.AddIndent((_932_r).dtor_content, _pat_let_tv86);
      }
      throw new System.Exception("unexpected control point");
    }
    public RAST._IExpr Then(RAST._IExpr rhs2) {
      if ((this).is_StmtExpr) {
        return RAST.Expr.create_StmtExpr((this).dtor_stmt, ((this).dtor_rhs).Then(rhs2));
      } else {
        return RAST.Expr.create_StmtExpr(this, rhs2);
      }
    }
    public RAST._IExpr Sel(Dafny.ISequence<Dafny.Rune> name) {
      return RAST.Expr.create_Select(this, name);
    }
    public RAST._IExpr MSel(Dafny.ISequence<Dafny.Rune> name) {
      return RAST.Expr.create_MemberSelect(this, name);
    }
    public RAST._IExpr Apply(Dafny.ISequence<RAST._IType> typeParameters, Dafny.ISequence<RAST._IExpr> arguments)
    {
      return RAST.Expr.create_Call(this, typeParameters, arguments);
    }
    public RAST._IExpr Apply1(RAST._IExpr argument) {
      return RAST.Expr.create_Call(this, Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IExpr>.FromElements(argument));
    }
    public RAST._IPrintingInfo printingInfo { get {
      RAST._IExpr _source36 = this;
      bool unmatched36 = true;
      if (unmatched36) {
        if (_source36.is_RawExpr) {
          Dafny.ISequence<Dafny.Rune> _933___v0 = _source36.dtor_content;
          unmatched36 = false;
          return RAST.PrintingInfo.create_UnknownPrecedence();
        }
      }
      if (unmatched36) {
        if (_source36.is_Identifier) {
          Dafny.ISequence<Dafny.Rune> _934___v1 = _source36.dtor_name;
          unmatched36 = false;
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      if (unmatched36) {
        if (_source36.is_LiteralInt) {
          Dafny.ISequence<Dafny.Rune> _935___v2 = _source36.dtor_value;
          unmatched36 = false;
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      if (unmatched36) {
        if (_source36.is_LiteralString) {
          Dafny.ISequence<Dafny.Rune> _936___v3 = _source36.dtor_value;
          bool _937___v4 = _source36.dtor_binary;
          unmatched36 = false;
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      if (unmatched36) {
        if (_source36.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> _938_op = _source36.dtor_op1;
          RAST._IExpr _939_underlying = _source36.dtor_underlying;
          DAST.Format._IUnaryOpFormat _940_format = _source36.dtor_format;
          unmatched36 = false;
          Dafny.ISequence<Dafny.Rune> _source37 = _938_op;
          bool unmatched37 = true;
          if (unmatched37) {
            if (_source37 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?")) {
              unmatched37 = false;
              return RAST.PrintingInfo.create_SuffixPrecedence(new BigInteger(5));
            }
          }
          if (unmatched37) {
            if (_source37 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")) {
              if (_source37 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")) {
                if (_source37 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!")) {
                  if (_source37 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) {
                    if (_source37 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut")) {
                      unmatched37 = false;
                      return RAST.PrintingInfo.create_Precedence(new BigInteger(6));
                    }
                  }
                }
              }
            }
          }
          if (unmatched37) {
            Dafny.ISequence<Dafny.Rune> _941___v5 = _source37;
            unmatched37 = false;
            return RAST.PrintingInfo.create_UnknownPrecedence();
          }
          throw new System.Exception("unexpected control point");
        }
      }
      if (unmatched36) {
        if (_source36.is_Select) {
          RAST._IExpr _942_underlying = _source36.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _943_name = _source36.dtor_name;
          unmatched36 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched36) {
        if (_source36.is_MemberSelect) {
          RAST._IExpr _944_underlying = _source36.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _945_name = _source36.dtor_name;
          unmatched36 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched36) {
        if (_source36.is_Call) {
          RAST._IExpr _946___v6 = _source36.dtor_obj;
          Dafny.ISequence<RAST._IType> _947___v7 = _source36.dtor_typeParameters;
          Dafny.ISequence<RAST._IExpr> _948___v8 = _source36.dtor_arguments;
          unmatched36 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched36) {
        if (_source36.is_TypeAscription) {
          RAST._IExpr _949_left = _source36.dtor_left;
          RAST._IType _950_tpe = _source36.dtor_tpe;
          unmatched36 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(10), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched36) {
        if (_source36.is_BinaryOp) {
          Dafny.ISequence<Dafny.Rune> _951_op2 = _source36.dtor_op2;
          RAST._IExpr _952_left = _source36.dtor_left;
          RAST._IExpr _953_right = _source36.dtor_right;
          DAST.Format._IBinaryOpFormat _954_format = _source36.dtor_format2;
          unmatched36 = false;
          Dafny.ISequence<Dafny.Rune> _source38 = _951_op2;
          bool unmatched38 = true;
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")) {
              if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")) {
                if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")) {
                  unmatched38 = false;
                  return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(20), RAST.Associativity.create_LeftToRight());
                }
              }
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")) {
              if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")) {
                unmatched38 = false;
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(30), RAST.Associativity.create_LeftToRight());
              }
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")) {
              if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")) {
                unmatched38 = false;
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(40), RAST.Associativity.create_LeftToRight());
              }
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) {
              unmatched38 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(50), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")) {
              unmatched38 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(60), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")) {
              unmatched38 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(70), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("==")) {
              if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!=")) {
                if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")) {
                  if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">")) {
                    if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<=")) {
                      if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">=")) {
                        unmatched38 = false;
                        return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses());
                      }
                    }
                  }
                }
              }
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")) {
              unmatched38 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(90), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")) {
              unmatched38 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(100), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..")) {
              if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..=")) {
                unmatched38 = false;
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RequiresParentheses());
              }
            }
          }
          if (unmatched38) {
            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=")) {
              if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+=")) {
                if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-=")) {
                  if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*=")) {
                    if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/=")) {
                      if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%=")) {
                        if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&=")) {
                          if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|=")) {
                            if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^=")) {
                              if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<=")) {
                                if (_source38 == Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>=")) {
                                  unmatched38 = false;
                                  return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          if (unmatched38) {
            Dafny.ISequence<Dafny.Rune> _955___v9 = _source38;
            unmatched38 = false;
            return RAST.PrintingInfo.create_PrecedenceAssociativity(BigInteger.Zero, RAST.Associativity.create_RequiresParentheses());
          }
          throw new System.Exception("unexpected control point");
        }
      }
      if (unmatched36) {
        RAST._IExpr _956___v10 = _source36;
        unmatched36 = false;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      }
      throw new System.Exception("unexpected control point");
    } }
  }
  public class Expr_RawExpr : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_content;
    public Expr_RawExpr(Dafny.ISequence<Dafny.Rune> content) : base() {
      this._i_content = content;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_RawExpr(_i_content);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_RawExpr;
      return oth != null && object.Equals(this._i_content, oth._i_content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.RawExpr";
      s += "(";
      s += this._i_content.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_Identifier : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public Expr_Identifier(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._i_name = name;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Identifier(_i_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Identifier;
      return oth != null && object.Equals(this._i_name, oth._i_name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Identifier";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_Match : Expr {
    public readonly RAST._IExpr _i_matchee;
    public readonly Dafny.ISequence<RAST._IMatchCase> _i_cases;
    public Expr_Match(RAST._IExpr matchee, Dafny.ISequence<RAST._IMatchCase> cases) : base() {
      this._i_matchee = matchee;
      this._i_cases = cases;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Match(_i_matchee, _i_cases);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Match;
      return oth != null && object.Equals(this._i_matchee, oth._i_matchee) && object.Equals(this._i_cases, oth._i_cases);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_matchee));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_cases));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Match";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_matchee);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_cases);
      s += ")";
      return s;
    }
  }
  public class Expr_StmtExpr : Expr {
    public readonly RAST._IExpr _i_stmt;
    public readonly RAST._IExpr _i_rhs;
    public Expr_StmtExpr(RAST._IExpr stmt, RAST._IExpr rhs) : base() {
      this._i_stmt = stmt;
      this._i_rhs = rhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_StmtExpr(_i_stmt, _i_rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_StmtExpr;
      return oth != null && object.Equals(this._i_stmt, oth._i_stmt) && object.Equals(this._i_rhs, oth._i_rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_stmt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.StmtExpr";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_stmt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_rhs);
      s += ")";
      return s;
    }
  }
  public class Expr_Block : Expr {
    public readonly RAST._IExpr _i_underlying;
    public Expr_Block(RAST._IExpr underlying) : base() {
      this._i_underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Block(_i_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Block;
      return oth != null && object.Equals(this._i_underlying, oth._i_underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Block";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_StructBuild : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<RAST._IAssignIdentifier> _i_assignments;
    public Expr_StructBuild(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IAssignIdentifier> assignments) : base() {
      this._i_name = name;
      this._i_assignments = assignments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_StructBuild(_i_name, _i_assignments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_StructBuild;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_assignments, oth._i_assignments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_assignments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.StructBuild";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_assignments);
      s += ")";
      return s;
    }
  }
  public class Expr_Tuple : Expr {
    public readonly Dafny.ISequence<RAST._IExpr> _i_arguments;
    public Expr_Tuple(Dafny.ISequence<RAST._IExpr> arguments) : base() {
      this._i_arguments = arguments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Tuple(_i_arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Tuple;
      return oth != null && object.Equals(this._i_arguments, oth._i_arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Tuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_arguments);
      s += ")";
      return s;
    }
  }
  public class Expr_UnaryOp : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_op1;
    public readonly RAST._IExpr _i_underlying;
    public readonly DAST.Format._IUnaryOpFormat _i_format;
    public Expr_UnaryOp(Dafny.ISequence<Dafny.Rune> op1, RAST._IExpr underlying, DAST.Format._IUnaryOpFormat format) : base() {
      this._i_op1 = op1;
      this._i_underlying = underlying;
      this._i_format = format;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_UnaryOp(_i_op1, _i_underlying, _i_format);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_UnaryOp;
      return oth != null && object.Equals(this._i_op1, oth._i_op1) && object.Equals(this._i_underlying, oth._i_underlying) && object.Equals(this._i_format, oth._i_format);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_op1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_underlying));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_format));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.UnaryOp";
      s += "(";
      s += this._i_op1.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_underlying);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_format);
      s += ")";
      return s;
    }
  }
  public class Expr_BinaryOp : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_op2;
    public readonly RAST._IExpr _i_left;
    public readonly RAST._IExpr _i_right;
    public readonly DAST.Format._IBinaryOpFormat _i_format2;
    public Expr_BinaryOp(Dafny.ISequence<Dafny.Rune> op2, RAST._IExpr left, RAST._IExpr right, DAST.Format._IBinaryOpFormat format2) : base() {
      this._i_op2 = op2;
      this._i_left = left;
      this._i_right = right;
      this._i_format2 = format2;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_BinaryOp(_i_op2, _i_left, _i_right, _i_format2);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_BinaryOp;
      return oth != null && object.Equals(this._i_op2, oth._i_op2) && object.Equals(this._i_left, oth._i_left) && object.Equals(this._i_right, oth._i_right) && object.Equals(this._i_format2, oth._i_format2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_op2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_right));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_format2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.BinaryOp";
      s += "(";
      s += this._i_op2.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_right);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_format2);
      s += ")";
      return s;
    }
  }
  public class Expr_TypeAscription : Expr {
    public readonly RAST._IExpr _i_left;
    public readonly RAST._IType _i_tpe;
    public Expr_TypeAscription(RAST._IExpr left, RAST._IType tpe) : base() {
      this._i_left = left;
      this._i_tpe = tpe;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_TypeAscription(_i_left, _i_tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_TypeAscription;
      return oth != null && object.Equals(this._i_left, oth._i_left) && object.Equals(this._i_tpe, oth._i_tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.TypeAscription";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_tpe);
      s += ")";
      return s;
    }
  }
  public class Expr_LiteralInt : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_value;
    public Expr_LiteralInt(Dafny.ISequence<Dafny.Rune> @value) : base() {
      this._i_value = @value;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_LiteralInt(_i_value);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_LiteralInt;
      return oth != null && object.Equals(this._i_value, oth._i_value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.LiteralInt";
      s += "(";
      s += this._i_value.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_LiteralString : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_value;
    public readonly bool _i_binary;
    public Expr_LiteralString(Dafny.ISequence<Dafny.Rune> @value, bool binary) : base() {
      this._i_value = @value;
      this._i_binary = binary;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_LiteralString(_i_value, _i_binary);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_LiteralString;
      return oth != null && object.Equals(this._i_value, oth._i_value) && this._i_binary == oth._i_binary;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_binary));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.LiteralString";
      s += "(";
      s += this._i_value.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_binary);
      s += ")";
      return s;
    }
  }
  public class Expr_ConversionNum : Expr {
    public readonly RAST._IType _i_tpe;
    public readonly RAST._IExpr _i_underlying;
    public Expr_ConversionNum(RAST._IType tpe, RAST._IExpr underlying) : base() {
      this._i_tpe = tpe;
      this._i_underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_ConversionNum(_i_tpe, _i_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_ConversionNum;
      return oth != null && object.Equals(this._i_tpe, oth._i_tpe) && object.Equals(this._i_underlying, oth._i_underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.ConversionNum";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_DeclareVar : Expr {
    public readonly RAST._IDeclareType _i_declareType;
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Std.Wrappers._IOption<RAST._IType> _i_optType;
    public readonly Std.Wrappers._IOption<RAST._IExpr> _i_optRhs;
    public Expr_DeclareVar(RAST._IDeclareType declareType, Dafny.ISequence<Dafny.Rune> name, Std.Wrappers._IOption<RAST._IType> optType, Std.Wrappers._IOption<RAST._IExpr> optRhs) : base() {
      this._i_declareType = declareType;
      this._i_name = name;
      this._i_optType = optType;
      this._i_optRhs = optRhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_DeclareVar(_i_declareType, _i_name, _i_optType, _i_optRhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_DeclareVar;
      return oth != null && object.Equals(this._i_declareType, oth._i_declareType) && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_optType, oth._i_optType) && object.Equals(this._i_optRhs, oth._i_optRhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_declareType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_optType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_optRhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.DeclareVar";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_declareType);
      s += ", ";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_optType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_optRhs);
      s += ")";
      return s;
    }
  }
  public class Expr_AssignVar : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly RAST._IExpr _i_rhs;
    public Expr_AssignVar(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr rhs) : base() {
      this._i_name = name;
      this._i_rhs = rhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_AssignVar(_i_name, _i_rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_AssignVar;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_rhs, oth._i_rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.AssignVar";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_rhs);
      s += ")";
      return s;
    }
  }
  public class Expr_IfExpr : Expr {
    public readonly RAST._IExpr _i_cond;
    public readonly RAST._IExpr _i_thn;
    public readonly RAST._IExpr _i_els;
    public Expr_IfExpr(RAST._IExpr cond, RAST._IExpr thn, RAST._IExpr els) : base() {
      this._i_cond = cond;
      this._i_thn = thn;
      this._i_els = els;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_IfExpr(_i_cond, _i_thn, _i_els);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_IfExpr;
      return oth != null && object.Equals(this._i_cond, oth._i_cond) && object.Equals(this._i_thn, oth._i_thn) && object.Equals(this._i_els, oth._i_els);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_thn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_els));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.IfExpr";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_thn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_els);
      s += ")";
      return s;
    }
  }
  public class Expr_Loop : Expr {
    public readonly Std.Wrappers._IOption<RAST._IExpr> _i_optCond;
    public readonly RAST._IExpr _i_underlying;
    public Expr_Loop(Std.Wrappers._IOption<RAST._IExpr> optCond, RAST._IExpr underlying) : base() {
      this._i_optCond = optCond;
      this._i_underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Loop(_i_optCond, _i_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Loop;
      return oth != null && object.Equals(this._i_optCond, oth._i_optCond) && object.Equals(this._i_underlying, oth._i_underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_optCond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Loop";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_optCond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_For : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly RAST._IExpr _i_range;
    public readonly RAST._IExpr _i_body;
    public Expr_For(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr range, RAST._IExpr body) : base() {
      this._i_name = name;
      this._i_range = range;
      this._i_body = body;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_For(_i_name, _i_range, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_For;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_range, oth._i_range) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_range));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.For";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_range);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
  }
  public class Expr_Labelled : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _i_lbl;
    public readonly RAST._IExpr _i_underlying;
    public Expr_Labelled(Dafny.ISequence<Dafny.Rune> lbl, RAST._IExpr underlying) : base() {
      this._i_lbl = lbl;
      this._i_underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Labelled(_i_lbl, _i_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Labelled;
      return oth != null && object.Equals(this._i_lbl, oth._i_lbl) && object.Equals(this._i_underlying, oth._i_underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_lbl));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Labelled";
      s += "(";
      s += this._i_lbl.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_Break : Expr {
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _i_optLbl;
    public Expr_Break(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) : base() {
      this._i_optLbl = optLbl;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Break(_i_optLbl);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Break;
      return oth != null && object.Equals(this._i_optLbl, oth._i_optLbl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_optLbl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Break";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_optLbl);
      s += ")";
      return s;
    }
  }
  public class Expr_Continue : Expr {
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _i_optLbl;
    public Expr_Continue(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) : base() {
      this._i_optLbl = optLbl;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Continue(_i_optLbl);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Continue;
      return oth != null && object.Equals(this._i_optLbl, oth._i_optLbl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_optLbl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Continue";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_optLbl);
      s += ")";
      return s;
    }
  }
  public class Expr_Return : Expr {
    public readonly Std.Wrappers._IOption<RAST._IExpr> _i_optExpr;
    public Expr_Return(Std.Wrappers._IOption<RAST._IExpr> optExpr) : base() {
      this._i_optExpr = optExpr;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Return(_i_optExpr);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Return;
      return oth != null && object.Equals(this._i_optExpr, oth._i_optExpr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_optExpr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Return";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_optExpr);
      s += ")";
      return s;
    }
  }
  public class Expr_Call : Expr {
    public readonly RAST._IExpr _i_obj;
    public readonly Dafny.ISequence<RAST._IType> _i_typeParameters;
    public readonly Dafny.ISequence<RAST._IExpr> _i_arguments;
    public Expr_Call(RAST._IExpr obj, Dafny.ISequence<RAST._IType> typeParameters, Dafny.ISequence<RAST._IExpr> arguments) : base() {
      this._i_obj = obj;
      this._i_typeParameters = typeParameters;
      this._i_arguments = arguments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Call(_i_obj, _i_typeParameters, _i_arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Call;
      return oth != null && object.Equals(this._i_obj, oth._i_obj) && object.Equals(this._i_typeParameters, oth._i_typeParameters) && object.Equals(this._i_arguments, oth._i_arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParameters));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_obj);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeParameters);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_arguments);
      s += ")";
      return s;
    }
  }
  public class Expr_Select : Expr {
    public readonly RAST._IExpr _i_obj;
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public Expr_Select(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) : base() {
      this._i_obj = obj;
      this._i_name = name;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Select(_i_obj, _i_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Select;
      return oth != null && object.Equals(this._i_obj, oth._i_obj) && object.Equals(this._i_name, oth._i_name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Select";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_obj);
      s += ", ";
      s += this._i_name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_MemberSelect : Expr {
    public readonly RAST._IExpr _i_obj;
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public Expr_MemberSelect(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) : base() {
      this._i_obj = obj;
      this._i_name = name;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_MemberSelect(_i_obj, _i_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_MemberSelect;
      return oth != null && object.Equals(this._i_obj, oth._i_obj) && object.Equals(this._i_name, oth._i_name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.MemberSelect";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_obj);
      s += ", ";
      s += this._i_name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public interface _IFn {
    bool is_Fn { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParam> dtor_typeParams { get; }
    Dafny.ISequence<RAST._IFormal> dtor_formals { get; }
    Std.Wrappers._IOption<RAST._IType> dtor_returnType { get; }
    Dafny.ISequence<Dafny.Rune> dtor_where { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_body { get; }
    _IFn DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Fn : _IFn {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<RAST._ITypeParam> _i_typeParams;
    public readonly Dafny.ISequence<RAST._IFormal> _i_formals;
    public readonly Std.Wrappers._IOption<RAST._IType> _i_returnType;
    public readonly Dafny.ISequence<Dafny.Rune> _i_where;
    public readonly Std.Wrappers._IOption<RAST._IExpr> _i_body;
    public Fn(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Dafny.ISequence<Dafny.Rune> @where, Std.Wrappers._IOption<RAST._IExpr> body) {
      this._i_name = name;
      this._i_typeParams = typeParams;
      this._i_formals = formals;
      this._i_returnType = returnType;
      this._i_where = @where;
      this._i_body = body;
    }
    public _IFn DowncastClone() {
      if (this is _IFn dt) { return dt; }
      return new Fn(_i_name, _i_typeParams, _i_formals, _i_returnType, _i_where, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Fn;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_formals, oth._i_formals) && object.Equals(this._i_returnType, oth._i_returnType) && object.Equals(this._i_where, oth._i_where) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_formals));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_returnType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_where));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Fn.Fn";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_formals);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_returnType);
      s += ", ";
      s += this._i_where.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
    private static readonly RAST._IFn theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParam>.Empty, Dafny.Sequence<RAST._IFormal>.Empty, Std.Wrappers.Option<RAST._IType>.Default(), Dafny.Sequence<Dafny.Rune>.Empty, Std.Wrappers.Option<RAST._IExpr>.Default());
    public static RAST._IFn Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IFn> _TYPE = new Dafny.TypeDescriptor<RAST._IFn>(RAST.Fn.Default());
    public static Dafny.TypeDescriptor<RAST._IFn> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFn create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Dafny.ISequence<Dafny.Rune> @where, Std.Wrappers._IOption<RAST._IExpr> body) {
      return new Fn(name, typeParams, formals, returnType, @where, body);
    }
    public static _IFn create_Fn(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Dafny.ISequence<Dafny.Rune> @where, Std.Wrappers._IOption<RAST._IExpr> body) {
      return create(name, typeParams, formals, returnType, @where, body);
    }
    public bool is_Fn { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParam> dtor_typeParams {
      get {
        return this._i_typeParams;
      }
    }
    public Dafny.ISequence<RAST._IFormal> dtor_formals {
      get {
        return this._i_formals;
      }
    }
    public Std.Wrappers._IOption<RAST._IType> dtor_returnType {
      get {
        return this._i_returnType;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_where {
      get {
        return this._i_where;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_body {
      get {
        return this._i_body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      var _pat_let_tv87 = ind;
      var _pat_let_tv88 = ind;
      var _pat_let_tv89 = ind;
      var _pat_let_tv90 = ind;
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn "), (this).dtor_name), RAST.TypeParam.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), RAST.__default.SeqToString<RAST._IFormal>((this).dtor_formals, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>>>((_957_ind) => ((System.Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>)((_958_formal) => {
        return (_958_formal)._ToString(_957_ind);
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), ((System.Func<Std.Wrappers._IOption<RAST._IType>, Dafny.ISequence<Dafny.Rune>>)((_source39) => {
        bool unmatched39 = true;
        if (unmatched39) {
          if (_source39.is_Some) {
            RAST._IType _959_t = _source39.dtor_value;
            unmatched39 = false;
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" -> "), (_959_t)._ToString(_pat_let_tv87));
          }
        }
        if (unmatched39) {
          Std.Wrappers._IOption<RAST._IType> _960___v29 = _source39;
          unmatched39 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        throw new System.Exception("unexpected control point");
      }))((this).dtor_returnType)), ((((this).dtor_where).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), (this).dtor_where)))), ((System.Func<Std.Wrappers._IOption<RAST._IExpr>, Dafny.ISequence<Dafny.Rune>>)((_source40) => {
        bool unmatched40 = true;
        if (unmatched40) {
          if (_source40.is_None) {
            unmatched40 = false;
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";");
          }
        }
        if (unmatched40) {
          RAST._IExpr _961_body = _source40.dtor_value;
          unmatched40 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"), _pat_let_tv88), RAST.__default.IND), (_961_body)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv89, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv90), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        throw new System.Exception("unexpected control point");
      }))((this).dtor_body));
    }
  }
} // end of namespace RAST