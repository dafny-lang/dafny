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
        BigInteger _828_i = Dafny.Helpers.Id<Func<__T, BigInteger>>(f)((s).Select(BigInteger.Zero));
        BigInteger _829_j = RAST.__default.SeqToHeight<__T>((s).Drop(BigInteger.One), f);
        if ((_828_i) < (_829_j)) {
          return _829_j;
        } else {
          return _828_i;
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
      Dafny.ISequence<Dafny.Rune> _830___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((raw).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_830___accumulator, raw);
      } else if ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[({")).Contains((raw).Select(BigInteger.Zero))) {
        _830___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_830___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in103 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in104 = Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND);
        raw = _in103;
        ind = _in104;
        goto TAIL_CALL_START;
      } else if (((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("})]")).Contains((raw).Select(BigInteger.Zero))) && ((new BigInteger((ind).Count)) > (new BigInteger(2)))) {
        _830___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_830___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in105 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in106 = (ind).Take((new BigInteger((ind).Count)) - (new BigInteger(2)));
        raw = _in105;
        ind = _in106;
        goto TAIL_CALL_START;
      } else if (((raw).Select(BigInteger.Zero)) == (new Dafny.Rune('\n'))) {
        _830___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_830___accumulator, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)), ind));
        Dafny.ISequence<Dafny.Rune> _in107 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in108 = ind;
        raw = _in107;
        ind = _in108;
        goto TAIL_CALL_START;
      } else {
        _830___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_830___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
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
        if (d is Mod_Mod) { return ((Mod_Mod)d)._name; }
        return ((Mod_ExternMod)d)._name;
      }
    }
    public Dafny.ISequence<RAST._IModDecl> dtor_body {
      get {
        var d = this;
        return ((Mod_Mod)d)._body;
      }
    }
    public abstract _IMod DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      RAST._IMod _source25 = this;
      if (_source25.is_Mod) {
        Dafny.ISequence<Dafny.Rune> _831___mcc_h0 = _source25.dtor_name;
        Dafny.ISequence<RAST._IModDecl> _832___mcc_h1 = _source25.dtor_body;
        Dafny.ISequence<RAST._IModDecl> _833_body = _832___mcc_h1;
        Dafny.ISequence<Dafny.Rune> _834_name = _831___mcc_h0;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod "), _834_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), RAST.__default.IND), RAST.__default.SeqToString<RAST._IModDecl>(_833_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IModDecl, Dafny.ISequence<Dafny.Rune>>>>((_835_ind) => ((System.Func<RAST._IModDecl, Dafny.ISequence<Dafny.Rune>>)((_836_modDecl) => {
          return (_836_modDecl)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_835_ind, RAST.__default.IND));
        })))(ind), Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else {
        Dafny.ISequence<Dafny.Rune> _837___mcc_h2 = _source25.dtor_name;
        Dafny.ISequence<Dafny.Rune> _838_name = _837___mcc_h2;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod "), _838_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
      }
    }
  }
  public class Mod_Mod : Mod {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._IModDecl> _body;
    public Mod_Mod(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IModDecl> body) : base() {
      this._name = name;
      this._body = body;
    }
    public override _IMod DowncastClone() {
      if (this is _IMod dt) { return dt; }
      return new Mod_Mod(_name, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Mod_Mod;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Mod.Mod";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class Mod_ExternMod : Mod {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Mod_ExternMod(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IMod DowncastClone() {
      if (this is _IMod dt) { return dt; }
      return new Mod_ExternMod(_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Mod_ExternMod;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Mod.ExternMod";
      s += "(";
      s += this._name.ToVerbatimString(true);
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
        return ((ModDecl_RawDecl)d)._body;
      }
    }
    public RAST._IMod dtor_mod {
      get {
        var d = this;
        return ((ModDecl_ModDecl)d)._mod;
      }
    }
    public RAST._IStruct dtor_struct {
      get {
        var d = this;
        return ((ModDecl_StructDecl)d)._struct;
      }
    }
    public RAST._IEnum dtor_enum {
      get {
        var d = this;
        return ((ModDecl_EnumDecl)d)._enum;
      }
    }
    public RAST._IImpl dtor_impl {
      get {
        var d = this;
        return ((ModDecl_ImplDecl)d)._impl;
      }
    }
    public RAST._ITrait dtor_tr {
      get {
        var d = this;
        return ((ModDecl_TraitDecl)d)._tr;
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
    public readonly Dafny.ISequence<Dafny.Rune> _body;
    public ModDecl_RawDecl(Dafny.ISequence<Dafny.Rune> body) : base() {
      this._body = body;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_RawDecl(_body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_RawDecl;
      return oth != null && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.RawDecl";
      s += "(";
      s += this._body.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ModDecl_ModDecl : ModDecl {
    public readonly RAST._IMod _mod;
    public ModDecl_ModDecl(RAST._IMod mod) : base() {
      this._mod = mod;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_ModDecl(_mod);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_ModDecl;
      return oth != null && object.Equals(this._mod, oth._mod);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._mod));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.ModDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._mod);
      s += ")";
      return s;
    }
  }
  public class ModDecl_StructDecl : ModDecl {
    public readonly RAST._IStruct _struct;
    public ModDecl_StructDecl(RAST._IStruct @struct) : base() {
      this._struct = @struct;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_StructDecl(_struct);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_StructDecl;
      return oth != null && object.Equals(this._struct, oth._struct);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._struct));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.StructDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._struct);
      s += ")";
      return s;
    }
  }
  public class ModDecl_EnumDecl : ModDecl {
    public readonly RAST._IEnum _enum;
    public ModDecl_EnumDecl(RAST._IEnum @enum) : base() {
      this._enum = @enum;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_EnumDecl(_enum);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_EnumDecl;
      return oth != null && object.Equals(this._enum, oth._enum);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._enum));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.EnumDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._enum);
      s += ")";
      return s;
    }
  }
  public class ModDecl_ImplDecl : ModDecl {
    public readonly RAST._IImpl _impl;
    public ModDecl_ImplDecl(RAST._IImpl impl) : base() {
      this._impl = impl;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_ImplDecl(_impl);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_ImplDecl;
      return oth != null && object.Equals(this._impl, oth._impl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._impl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.ImplDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._impl);
      s += ")";
      return s;
    }
  }
  public class ModDecl_TraitDecl : ModDecl {
    public readonly RAST._ITrait _tr;
    public ModDecl_TraitDecl(RAST._ITrait tr) : base() {
      this._tr = tr;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_TraitDecl(_tr);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_TraitDecl;
      return oth != null && object.Equals(this._tr, oth._tr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.TraitDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._tr);
      s += ")";
      return s;
    }
  }

  public interface _IAttribute {
    bool is_RawAttribute { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
  }
  public class Attribute : _IAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _content;
    public Attribute(Dafny.ISequence<Dafny.Rune> content) {
      this._content = content;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Attribute;
      return oth != null && object.Equals(this._content, oth._content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Attribute.RawAttribute";
      s += "(";
      s += this._content.ToVerbatimString(true);
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
        return this._content;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ToStringMultiple(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> ind)
    {
      return RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(attributes, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>>((_839_ind) => ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_840_attribute) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_840_attribute), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _839_ind);
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
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParam> _typeParams;
    public readonly RAST._IFormals _fields;
    public Struct(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IFormals fields) {
      this._attributes = attributes;
      this._name = name;
      this._typeParams = typeParams;
      this._fields = fields;
    }
    public _IStruct DowncastClone() {
      if (this is _IStruct dt) { return dt; }
      return new Struct(_attributes, _name, _typeParams, _fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Struct;
      return oth != null && object.Equals(this._attributes, oth._attributes) && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._fields, oth._fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Struct.Struct";
      s += "(";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fields);
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
        return this._attributes;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParam> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public RAST._IFormals dtor_fields {
      get {
        return this._fields;
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
    public readonly RAST._IVisibility _visibility;
    public readonly RAST._IType _tpe;
    public NamelessFormal(RAST._IVisibility visibility, RAST._IType tpe) {
      this._visibility = visibility;
      this._tpe = tpe;
    }
    public _INamelessFormal DowncastClone() {
      if (this is _INamelessFormal dt) { return dt; }
      return new NamelessFormal(_visibility, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.NamelessFormal;
      return oth != null && object.Equals(this._visibility, oth._visibility) && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visibility));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.NamelessFormal.NamelessFormal";
      s += "(";
      s += Dafny.Helpers.ToString(this._visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
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
        return this._visibility;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
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
        return ((Formals_NamedFormals)d)._fields;
      }
    }
    public Dafny.ISequence<RAST._INamelessFormal> dtor_types {
      get {
        var d = this;
        return ((Formals_NamelessFormals)d)._types;
      }
    }
    public abstract _IFormals DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine)
    {
      if ((this).is_NamedFormals) {
        Dafny.ISequence<Dafny.Rune> _841_separator = ((newLine) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")));
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs40 = (((newLine) && ((new BigInteger(((this).dtor_fields).Count)).Sign == 1)) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind))) : ((((new BigInteger(((this).dtor_fields).Count)).Sign == 1) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))) : (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
        Dafny.ISequence<Dafny.Rune> _842_beginSpace = _let_tmp_rhs40.dtor__0;
        Dafny.ISequence<Dafny.Rune> _843_endSpace = _let_tmp_rhs40.dtor__1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"), _842_beginSpace), RAST.__default.SeqToString<RAST._IFormal>((this).dtor_fields, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>>>((_844_ind) => ((System.Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>)((_845_field) => {
          return (_845_field)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_844_ind, RAST.__default.IND));
        })))(ind), _841_separator)), _843_endSpace), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else {
        Dafny.ISequence<Dafny.Rune> _846_separator = ((newLine) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")));
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._INamelessFormal>((this).dtor_types, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._INamelessFormal, Dafny.ISequence<Dafny.Rune>>>>((_847_ind) => ((System.Func<RAST._INamelessFormal, Dafny.ISequence<Dafny.Rune>>)((_848_t) => {
          return (_848_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_847_ind, RAST.__default.IND));
        })))(ind), _846_separator)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
    }
  }
  public class Formals_NamedFormals : Formals {
    public readonly Dafny.ISequence<RAST._IFormal> _fields;
    public Formals_NamedFormals(Dafny.ISequence<RAST._IFormal> fields) : base() {
      this._fields = fields;
    }
    public override _IFormals DowncastClone() {
      if (this is _IFormals dt) { return dt; }
      return new Formals_NamedFormals(_fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Formals_NamedFormals;
      return oth != null && object.Equals(this._fields, oth._fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Formals.NamedFormals";
      s += "(";
      s += Dafny.Helpers.ToString(this._fields);
      s += ")";
      return s;
    }
  }
  public class Formals_NamelessFormals : Formals {
    public readonly Dafny.ISequence<RAST._INamelessFormal> _types;
    public Formals_NamelessFormals(Dafny.ISequence<RAST._INamelessFormal> types) : base() {
      this._types = types;
    }
    public override _IFormals DowncastClone() {
      if (this is _IFormals dt) { return dt; }
      return new Formals_NamelessFormals(_types);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Formals_NamelessFormals;
      return oth != null && object.Equals(this._types, oth._types);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._types));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Formals.NamelessFormals";
      s += "(";
      s += Dafny.Helpers.ToString(this._types);
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IFormals _fields;
    public EnumCase(Dafny.ISequence<Dafny.Rune> name, RAST._IFormals fields) {
      this._name = name;
      this._fields = fields;
    }
    public _IEnumCase DowncastClone() {
      if (this is _IEnumCase dt) { return dt; }
      return new EnumCase(_name, _fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.EnumCase;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._fields, oth._fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.EnumCase.EnumCase";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fields);
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
        return this._name;
      }
    }
    public RAST._IFormals dtor_fields {
      get {
        return this._fields;
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
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParam> _typeParams;
    public readonly Dafny.ISequence<RAST._IEnumCase> _variants;
    public Enum(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
      this._attributes = attributes;
      this._name = name;
      this._typeParams = typeParams;
      this._variants = variants;
    }
    public _IEnum DowncastClone() {
      if (this is _IEnum dt) { return dt; }
      return new Enum(_attributes, _name, _typeParams, _variants);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Enum;
      return oth != null && object.Equals(this._attributes, oth._attributes) && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._variants, oth._variants);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._variants));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Enum.Enum";
      s += "(";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._variants);
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
        return this._attributes;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParam> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<RAST._IEnumCase> dtor_variants {
      get {
        return this._variants;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub enum ")), (this).dtor_name), RAST.TypeParam.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IEnumCase>((this).dtor_variants, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IEnumCase, Dafny.ISequence<Dafny.Rune>>>>((_849_ind) => ((System.Func<RAST._IEnumCase, Dafny.ISequence<Dafny.Rune>>)((_850_variant) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _849_ind), RAST.__default.IND), (_850_variant)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_849_ind, RAST.__default.IND), false));
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
    public readonly Dafny.ISequence<Dafny.Rune> _content;
    public readonly Dafny.ISequence<RAST._IType> _constraints;
    public TypeParam(Dafny.ISequence<Dafny.Rune> content, Dafny.ISequence<RAST._IType> constraints) {
      this._content = content;
      this._constraints = constraints;
    }
    public _ITypeParam DowncastClone() {
      if (this is _ITypeParam dt) { return dt; }
      return new TypeParam(_content, _constraints);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.TypeParam;
      return oth != null && object.Equals(this._content, oth._content) && object.Equals(this._constraints, oth._constraints);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._content));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._constraints));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.TypeParam.RawTypeParam";
      s += "(";
      s += this._content.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._constraints);
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
        return this._content;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_constraints {
      get {
        return this._constraints;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ToStringMultiple(Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<Dafny.Rune> ind)
    {
      if ((new BigInteger((typeParams).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), RAST.__default.SeqToString<RAST._ITypeParam>(typeParams, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._ITypeParam, Dafny.ISequence<Dafny.Rune>>>>((_851_ind) => ((System.Func<RAST._ITypeParam, Dafny.ISequence<Dafny.Rune>>)((_852_t) => {
          return (_852_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_851_ind, RAST.__default.IND));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
    }
    public static Dafny.ISequence<RAST._ITypeParam> AddConstraintsMultiple(Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IType> constraints)
    {
      Dafny.ISequence<RAST._ITypeParam> _853___accumulator = Dafny.Sequence<RAST._ITypeParam>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((typeParams).Count)).Sign == 0) {
        return Dafny.Sequence<RAST._ITypeParam>.Concat(_853___accumulator, Dafny.Sequence<RAST._ITypeParam>.FromElements());
      } else {
        _853___accumulator = Dafny.Sequence<RAST._ITypeParam>.Concat(_853___accumulator, Dafny.Sequence<RAST._ITypeParam>.FromElements(((typeParams).Select(BigInteger.Zero)).AddConstraints(constraints)));
        Dafny.ISequence<RAST._ITypeParam> _in111 = (typeParams).Drop(BigInteger.One);
        Dafny.ISequence<RAST._IType> _in112 = constraints;
        typeParams = _in111;
        constraints = _in112;
        goto TAIL_CALL_START;
      }
    }
    public RAST._ITypeParam AddConstraints(Dafny.ISequence<RAST._IType> constraints) {
      RAST._ITypeParam _854_dt__update__tmp_h0 = this;
      Dafny.ISequence<RAST._IType> _855_dt__update_hconstraints_h0 = Dafny.Sequence<RAST._IType>.Concat((this).dtor_constraints, constraints);
      return RAST.TypeParam.create((_854_dt__update__tmp_h0).dtor_content, _855_dt__update_hconstraints_h0);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_content, (((new BigInteger(((this).dtor_constraints).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), RAST.__default.SeqToString<RAST._IType>((this).dtor_constraints, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_856_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_857_t) => {
        return (_857_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_856_ind, RAST.__default.IND));
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
        if (d is Type_TIdentifier) { return ((Type_TIdentifier)d)._name; }
        return ((Type_TMemberSelect)d)._name;
      }
    }
    public RAST._IType dtor_base {
      get {
        var d = this;
        return ((Type_TMemberSelect)d)._base;
      }
    }
    public RAST._IType dtor_baseName {
      get {
        var d = this;
        return ((Type_TypeApp)d)._baseName;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_arguments {
      get {
        var d = this;
        if (d is Type_TypeApp) { return ((Type_TypeApp)d)._arguments; }
        if (d is Type_TupleType) { return ((Type_TupleType)d)._arguments; }
        return ((Type_FnType)d)._arguments;
      }
    }
    public RAST._IType dtor_underlying {
      get {
        var d = this;
        if (d is Type_Borrowed) { return ((Type_Borrowed)d)._underlying; }
        if (d is Type_BorrowedMut) { return ((Type_BorrowedMut)d)._underlying; }
        if (d is Type_ImplType) { return ((Type_ImplType)d)._underlying; }
        return ((Type_DynType)d)._underlying;
      }
    }
    public RAST._IType dtor_returnType {
      get {
        var d = this;
        return ((Type_FnType)d)._returnType;
      }
    }
    public RAST._IType dtor_left {
      get {
        var d = this;
        return ((Type_IntersectionType)d)._left;
      }
    }
    public RAST._IType dtor_right {
      get {
        var d = this;
        return ((Type_IntersectionType)d)._right;
      }
    }
    public abstract _IType DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      RAST._IType _source26 = this;
      if (_source26.is_SelfOwned) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
      } else if (_source26.is_U8) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8");
      } else if (_source26.is_U16) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16");
      } else if (_source26.is_U32) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32");
      } else if (_source26.is_U64) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64");
      } else if (_source26.is_U128) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128");
      } else if (_source26.is_I8) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8");
      } else if (_source26.is_I16) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16");
      } else if (_source26.is_I32) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32");
      } else if (_source26.is_I64) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64");
      } else if (_source26.is_I128) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128");
      } else if (_source26.is_TIdentifier) {
        Dafny.ISequence<Dafny.Rune> _858___mcc_h0 = _source26.dtor_name;
        Dafny.ISequence<Dafny.Rune> _859_underlying = _858___mcc_h0;
        return _859_underlying;
      } else if (_source26.is_TMemberSelect) {
        RAST._IType _860___mcc_h1 = _source26.dtor_base;
        Dafny.ISequence<Dafny.Rune> _861___mcc_h2 = _source26.dtor_name;
        Dafny.ISequence<Dafny.Rune> _862_name = _861___mcc_h2;
        RAST._IType _863_underlying = _860___mcc_h1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_863_underlying)._ToString(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _862_name);
      } else if (_source26.is_TypeApp) {
        RAST._IType _864___mcc_h3 = _source26.dtor_baseName;
        Dafny.ISequence<RAST._IType> _865___mcc_h4 = _source26.dtor_arguments;
        Dafny.ISequence<RAST._IType> _866_args = _865___mcc_h4;
        RAST._IType _867_base = _864___mcc_h3;
        return Dafny.Sequence<Dafny.Rune>.Concat((_867_base)._ToString(ind), (((_866_args).Equals(Dafny.Sequence<RAST._IType>.FromElements())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), RAST.__default.SeqToString<RAST._IType>(_866_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_868_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_869_arg) => {
          return (_869_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_868_ind, RAST.__default.IND));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">")))));
      } else if (_source26.is_Borrowed) {
        RAST._IType _870___mcc_h5 = _source26.dtor_underlying;
        RAST._IType _871_underlying = _870___mcc_h5;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), (_871_underlying)._ToString(ind));
      } else if (_source26.is_BorrowedMut) {
        RAST._IType _872___mcc_h6 = _source26.dtor_underlying;
        RAST._IType _873_underlying = _872___mcc_h6;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut "), (_873_underlying)._ToString(ind));
      } else if (_source26.is_ImplType) {
        RAST._IType _874___mcc_h7 = _source26.dtor_underlying;
        RAST._IType _875_underlying = _874___mcc_h7;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), (_875_underlying)._ToString(ind));
      } else if (_source26.is_DynType) {
        RAST._IType _876___mcc_h8 = _source26.dtor_underlying;
        RAST._IType _877_underlying = _876___mcc_h8;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn "), (_877_underlying)._ToString(ind));
      } else if (_source26.is_TupleType) {
        Dafny.ISequence<RAST._IType> _878___mcc_h9 = _source26.dtor_arguments;
        Dafny.ISequence<RAST._IType> _879_args = _878___mcc_h9;
        if ((_879_args).Equals(Dafny.Sequence<RAST._IType>.FromElements())) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()");
        } else {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._IType>(_879_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_880_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_881_arg) => {
            return (_881_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_880_ind, RAST.__default.IND));
          })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      } else if (_source26.is_FnType) {
        Dafny.ISequence<RAST._IType> _882___mcc_h10 = _source26.dtor_arguments;
        RAST._IType _883___mcc_h11 = _source26.dtor_returnType;
        RAST._IType _884_returnType = _883___mcc_h11;
        Dafny.ISequence<RAST._IType> _885_arguments = _882___mcc_h10;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Fn("), RAST.__default.SeqToString<RAST._IType>(_885_arguments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_886_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_887_arg) => {
          return (_887_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_886_ind, RAST.__default.IND));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), (_884_returnType)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)));
      } else {
        RAST._IType _888___mcc_h12 = _source26.dtor_left;
        RAST._IType _889___mcc_h13 = _source26.dtor_right;
        RAST._IType _890_right = _889___mcc_h13;
        RAST._IType _891_left = _888___mcc_h12;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_891_left)._ToString(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + ")), (_890_right)._ToString(ind));
      }
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Type_TIdentifier(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TIdentifier(_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TIdentifier;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TIdentifier";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Type_TMemberSelect : Type {
    public readonly RAST._IType _base;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Type_TMemberSelect(RAST._IType @base, Dafny.ISequence<Dafny.Rune> name) : base() {
      this._base = @base;
      this._name = name;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TMemberSelect(_base, _name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TMemberSelect;
      return oth != null && object.Equals(this._base, oth._base) && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._base));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TMemberSelect";
      s += "(";
      s += Dafny.Helpers.ToString(this._base);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Type_TypeApp : Type {
    public readonly RAST._IType _baseName;
    public readonly Dafny.ISequence<RAST._IType> _arguments;
    public Type_TypeApp(RAST._IType baseName, Dafny.ISequence<RAST._IType> arguments) : base() {
      this._baseName = baseName;
      this._arguments = arguments;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TypeApp(_baseName, _arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TypeApp;
      return oth != null && object.Equals(this._baseName, oth._baseName) && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._baseName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TypeApp";
      s += "(";
      s += Dafny.Helpers.ToString(this._baseName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ")";
      return s;
    }
  }
  public class Type_Borrowed : Type {
    public readonly RAST._IType _underlying;
    public Type_Borrowed(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Borrowed(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_Borrowed;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.Borrowed";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Type_BorrowedMut : Type {
    public readonly RAST._IType _underlying;
    public Type_BorrowedMut(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_BorrowedMut(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_BorrowedMut;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.BorrowedMut";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Type_ImplType : Type {
    public readonly RAST._IType _underlying;
    public Type_ImplType(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_ImplType(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_ImplType;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.ImplType";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Type_DynType : Type {
    public readonly RAST._IType _underlying;
    public Type_DynType(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_DynType(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_DynType;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.DynType";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Type_TupleType : Type {
    public readonly Dafny.ISequence<RAST._IType> _arguments;
    public Type_TupleType(Dafny.ISequence<RAST._IType> arguments) : base() {
      this._arguments = arguments;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TupleType(_arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TupleType;
      return oth != null && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TupleType";
      s += "(";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ")";
      return s;
    }
  }
  public class Type_FnType : Type {
    public readonly Dafny.ISequence<RAST._IType> _arguments;
    public readonly RAST._IType _returnType;
    public Type_FnType(Dafny.ISequence<RAST._IType> arguments, RAST._IType returnType) : base() {
      this._arguments = arguments;
      this._returnType = returnType;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_FnType(_arguments, _returnType);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_FnType;
      return oth != null && object.Equals(this._arguments, oth._arguments) && object.Equals(this._returnType, oth._returnType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._returnType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.FnType";
      s += "(";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ", ";
      s += Dafny.Helpers.ToString(this._returnType);
      s += ")";
      return s;
    }
  }
  public class Type_IntersectionType : Type {
    public readonly RAST._IType _left;
    public readonly RAST._IType _right;
    public Type_IntersectionType(RAST._IType left, RAST._IType right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_IntersectionType(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_IntersectionType;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.IntersectionType";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
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
    public readonly Dafny.ISequence<RAST._ITypeParam> _typeParams;
    public readonly RAST._IType _tpe;
    public readonly Dafny.ISequence<Dafny.Rune> _where;
    public readonly Dafny.ISequence<RAST._IImplMember> _body;
    public Trait(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) {
      this._typeParams = typeParams;
      this._tpe = tpe;
      this._where = @where;
      this._body = body;
    }
    public _ITrait DowncastClone() {
      if (this is _ITrait dt) { return dt; }
      return new Trait(_typeParams, _tpe, _where, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Trait;
      return oth != null && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._where, oth._where) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._where));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Trait.Trait";
      s += "(";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += this._where.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
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
        return this._typeParams;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_where {
      get {
        return this._where;
      }
    }
    public Dafny.ISequence<RAST._IImplMember> dtor_body {
      get {
        return this._body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait "), RAST.TypeParam.ToStringMultiple((this).dtor_typeParams, ind)), ((this).dtor_tpe)._ToString(ind)), ((!((this).dtor_where).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), (this).dtor_where)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IImplMember>((this).dtor_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>>>((_892_ind) => ((System.Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>)((_893_member) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _892_ind), RAST.__default.IND), (_893_member)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_892_ind, RAST.__default.IND)));
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
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._typeParams; }
        return ((Impl_Impl)d)._typeParams;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._tpe; }
        return ((Impl_Impl)d)._tpe;
      }
    }
    public RAST._IType dtor_forType {
      get {
        var d = this;
        return ((Impl_ImplFor)d)._forType;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_where {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._where; }
        return ((Impl_Impl)d)._where;
      }
    }
    public Dafny.ISequence<RAST._IImplMember> dtor_body {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._body; }
        return ((Impl_Impl)d)._body;
      }
    }
    public abstract _IImpl DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), RAST.TypeParam.ToStringMultiple((this).dtor_typeParams, ind)), ((this).dtor_tpe)._ToString(ind)), (((this).is_ImplFor) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" for "), ((this).dtor_forType)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), ((!((this).dtor_where).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), (this).dtor_where)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IImplMember>((this).dtor_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>>>((_894_ind) => ((System.Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>)((_895_member) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _894_ind), RAST.__default.IND), (_895_member)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_894_ind, RAST.__default.IND)));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (((new BigInteger(((this).dtor_body).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }
  public class Impl_ImplFor : Impl {
    public readonly Dafny.ISequence<RAST._ITypeParam> _typeParams;
    public readonly RAST._IType _tpe;
    public readonly RAST._IType _forType;
    public readonly Dafny.ISequence<Dafny.Rune> _where;
    public readonly Dafny.ISequence<RAST._IImplMember> _body;
    public Impl_ImplFor(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, RAST._IType forType, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) : base() {
      this._typeParams = typeParams;
      this._tpe = tpe;
      this._forType = forType;
      this._where = @where;
      this._body = body;
    }
    public override _IImpl DowncastClone() {
      if (this is _IImpl dt) { return dt; }
      return new Impl_ImplFor(_typeParams, _tpe, _forType, _where, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Impl_ImplFor;
      return oth != null && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._forType, oth._forType) && object.Equals(this._where, oth._where) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._forType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._where));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Impl.ImplFor";
      s += "(";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._forType);
      s += ", ";
      s += this._where.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class Impl_Impl : Impl {
    public readonly Dafny.ISequence<RAST._ITypeParam> _typeParams;
    public readonly RAST._IType _tpe;
    public readonly Dafny.ISequence<Dafny.Rune> _where;
    public readonly Dafny.ISequence<RAST._IImplMember> _body;
    public Impl_Impl(Dafny.ISequence<RAST._ITypeParam> typeParams, RAST._IType tpe, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) : base() {
      this._typeParams = typeParams;
      this._tpe = tpe;
      this._where = @where;
      this._body = body;
    }
    public override _IImpl DowncastClone() {
      if (this is _IImpl dt) { return dt; }
      return new Impl_Impl(_typeParams, _tpe, _where, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Impl_Impl;
      return oth != null && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._where, oth._where) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._where));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Impl.Impl";
      s += "(";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += this._where.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
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
        return ((ImplMember_RawImplMember)d)._content;
      }
    }
    public RAST._IVisibility dtor_pub {
      get {
        var d = this;
        return ((ImplMember_FnDecl)d)._pub;
      }
    }
    public RAST._IFn dtor_fun {
      get {
        var d = this;
        return ((ImplMember_FnDecl)d)._fun;
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
    public readonly Dafny.ISequence<Dafny.Rune> _content;
    public ImplMember_RawImplMember(Dafny.ISequence<Dafny.Rune> content) : base() {
      this._content = content;
    }
    public override _IImplMember DowncastClone() {
      if (this is _IImplMember dt) { return dt; }
      return new ImplMember_RawImplMember(_content);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ImplMember_RawImplMember;
      return oth != null && object.Equals(this._content, oth._content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ImplMember.RawImplMember";
      s += "(";
      s += this._content.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ImplMember_FnDecl : ImplMember {
    public readonly RAST._IVisibility _pub;
    public readonly RAST._IFn _fun;
    public ImplMember_FnDecl(RAST._IVisibility pub, RAST._IFn fun) : base() {
      this._pub = pub;
      this._fun = fun;
    }
    public override _IImplMember DowncastClone() {
      if (this is _IImplMember dt) { return dt; }
      return new ImplMember_FnDecl(_pub, _fun);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ImplMember_FnDecl;
      return oth != null && object.Equals(this._pub, oth._pub) && object.Equals(this._fun, oth._fun);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pub));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fun));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ImplMember.FnDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._pub);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fun);
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IType _tpe;
    public Formal(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe) {
      this._name = name;
      this._tpe = tpe;
    }
    public _IFormal DowncastClone() {
      if (this is _IFormal dt) { return dt; }
      return new Formal(_name, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Formal;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Formal.Formal";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
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
        return this._name;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
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
    public readonly Dafny.ISequence<Dafny.Rune> _content;
    public Pattern(Dafny.ISequence<Dafny.Rune> content) {
      this._content = content;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Pattern;
      return oth != null && object.Equals(this._content, oth._content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Pattern.RawPattern";
      s += "(";
      s += this._content.ToVerbatimString(true);
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
        return this._content;
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
    public readonly Dafny.ISequence<Dafny.Rune> _pattern;
    public readonly RAST._IExpr _rhs;
    public MatchCase(Dafny.ISequence<Dafny.Rune> pattern, RAST._IExpr rhs) {
      this._pattern = pattern;
      this._rhs = rhs;
    }
    public _IMatchCase DowncastClone() {
      if (this is _IMatchCase dt) { return dt; }
      return new MatchCase(_pattern, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.MatchCase;
      return oth != null && object.Equals(this._pattern, oth._pattern) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pattern));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.MatchCase.MatchCase";
      s += "(";
      s += Dafny.Helpers.ToString(this._pattern);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rhs);
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
        return this._pattern;
      }
    }
    public RAST._IExpr dtor_rhs {
      get {
        return this._rhs;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      Dafny.ISequence<Dafny.Rune> _896_newIndent = ((((this).dtor_rhs).is_Block) ? (ind) : (Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)));
      Dafny.ISequence<Dafny.Rune> _897_rhsString = ((this).dtor_rhs)._ToString(_896_newIndent);
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Pattern._ToString((this).dtor_pattern, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" =>")), ((((_897_rhsString).Contains(new Dafny.Rune('\n'))) && (((_897_rhsString).Select(BigInteger.Zero)) != (new Dafny.Rune('{')))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), _897_rhsString)) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), _897_rhsString))));
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
    public readonly Dafny.ISequence<Dafny.Rune> _identifier;
    public readonly RAST._IExpr _rhs;
    public AssignIdentifier(Dafny.ISequence<Dafny.Rune> identifier, RAST._IExpr rhs) {
      this._identifier = identifier;
      this._rhs = rhs;
    }
    public _IAssignIdentifier DowncastClone() {
      if (this is _IAssignIdentifier dt) { return dt; }
      return new AssignIdentifier(_identifier, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignIdentifier;
      return oth != null && object.Equals(this._identifier, oth._identifier) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._identifier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignIdentifier.AssignIdentifier";
      s += "(";
      s += this._identifier.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rhs);
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
        return this._identifier;
      }
    }
    public RAST._IExpr dtor_rhs {
      get {
        return this._rhs;
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
        if (d is PrintingInfo_Precedence) { return ((PrintingInfo_Precedence)d)._precedence; }
        if (d is PrintingInfo_SuffixPrecedence) { return ((PrintingInfo_SuffixPrecedence)d)._precedence; }
        return ((PrintingInfo_PrecedenceAssociativity)d)._precedence;
      }
    }
    public RAST._IAssociativity dtor_associativity {
      get {
        var d = this;
        return ((PrintingInfo_PrecedenceAssociativity)d)._associativity;
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
    public readonly BigInteger _precedence;
    public PrintingInfo_Precedence(BigInteger precedence) : base() {
      this._precedence = precedence;
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_Precedence(_precedence);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_Precedence;
      return oth != null && this._precedence == oth._precedence;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._precedence));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.Precedence";
      s += "(";
      s += Dafny.Helpers.ToString(this._precedence);
      s += ")";
      return s;
    }
  }
  public class PrintingInfo_SuffixPrecedence : PrintingInfo {
    public readonly BigInteger _precedence;
    public PrintingInfo_SuffixPrecedence(BigInteger precedence) : base() {
      this._precedence = precedence;
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_SuffixPrecedence(_precedence);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_SuffixPrecedence;
      return oth != null && this._precedence == oth._precedence;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._precedence));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.SuffixPrecedence";
      s += "(";
      s += Dafny.Helpers.ToString(this._precedence);
      s += ")";
      return s;
    }
  }
  public class PrintingInfo_PrecedenceAssociativity : PrintingInfo {
    public readonly BigInteger _precedence;
    public readonly RAST._IAssociativity _associativity;
    public PrintingInfo_PrecedenceAssociativity(BigInteger precedence, RAST._IAssociativity associativity) : base() {
      this._precedence = precedence;
      this._associativity = associativity;
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_PrecedenceAssociativity(_precedence, _associativity);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_PrecedenceAssociativity;
      return oth != null && this._precedence == oth._precedence && object.Equals(this._associativity, oth._associativity);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._precedence));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._associativity));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.PrecedenceAssociativity";
      s += "(";
      s += Dafny.Helpers.ToString(this._precedence);
      s += ", ";
      s += Dafny.Helpers.ToString(this._associativity);
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
        return ((Expr_RawExpr)d)._content;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Expr_Identifier) { return ((Expr_Identifier)d)._name; }
        if (d is Expr_StructBuild) { return ((Expr_StructBuild)d)._name; }
        if (d is Expr_DeclareVar) { return ((Expr_DeclareVar)d)._name; }
        if (d is Expr_AssignVar) { return ((Expr_AssignVar)d)._name; }
        if (d is Expr_For) { return ((Expr_For)d)._name; }
        if (d is Expr_Select) { return ((Expr_Select)d)._name; }
        return ((Expr_MemberSelect)d)._name;
      }
    }
    public RAST._IExpr dtor_matchee {
      get {
        var d = this;
        return ((Expr_Match)d)._matchee;
      }
    }
    public Dafny.ISequence<RAST._IMatchCase> dtor_cases {
      get {
        var d = this;
        return ((Expr_Match)d)._cases;
      }
    }
    public RAST._IExpr dtor_stmt {
      get {
        var d = this;
        return ((Expr_StmtExpr)d)._stmt;
      }
    }
    public RAST._IExpr dtor_rhs {
      get {
        var d = this;
        if (d is Expr_StmtExpr) { return ((Expr_StmtExpr)d)._rhs; }
        return ((Expr_AssignVar)d)._rhs;
      }
    }
    public RAST._IExpr dtor_underlying {
      get {
        var d = this;
        if (d is Expr_Block) { return ((Expr_Block)d)._underlying; }
        if (d is Expr_UnaryOp) { return ((Expr_UnaryOp)d)._underlying; }
        if (d is Expr_ConversionNum) { return ((Expr_ConversionNum)d)._underlying; }
        if (d is Expr_Loop) { return ((Expr_Loop)d)._underlying; }
        return ((Expr_Labelled)d)._underlying;
      }
    }
    public Dafny.ISequence<RAST._IAssignIdentifier> dtor_assignments {
      get {
        var d = this;
        return ((Expr_StructBuild)d)._assignments;
      }
    }
    public Dafny.ISequence<RAST._IExpr> dtor_arguments {
      get {
        var d = this;
        if (d is Expr_Tuple) { return ((Expr_Tuple)d)._arguments; }
        return ((Expr_Call)d)._arguments;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_op1 {
      get {
        var d = this;
        return ((Expr_UnaryOp)d)._op1;
      }
    }
    public DAST.Format._IUnaryOpFormat dtor_format {
      get {
        var d = this;
        return ((Expr_UnaryOp)d)._format;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_op2 {
      get {
        var d = this;
        return ((Expr_BinaryOp)d)._op2;
      }
    }
    public RAST._IExpr dtor_left {
      get {
        var d = this;
        if (d is Expr_BinaryOp) { return ((Expr_BinaryOp)d)._left; }
        return ((Expr_TypeAscription)d)._left;
      }
    }
    public RAST._IExpr dtor_right {
      get {
        var d = this;
        return ((Expr_BinaryOp)d)._right;
      }
    }
    public DAST.Format._IBinaryOpFormat dtor_format2 {
      get {
        var d = this;
        return ((Expr_BinaryOp)d)._format2;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        var d = this;
        if (d is Expr_TypeAscription) { return ((Expr_TypeAscription)d)._tpe; }
        return ((Expr_ConversionNum)d)._tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_value {
      get {
        var d = this;
        if (d is Expr_LiteralInt) { return ((Expr_LiteralInt)d)._value; }
        return ((Expr_LiteralString)d)._value;
      }
    }
    public bool dtor_binary {
      get {
        var d = this;
        return ((Expr_LiteralString)d)._binary;
      }
    }
    public RAST._IDeclareType dtor_declareType {
      get {
        var d = this;
        return ((Expr_DeclareVar)d)._declareType;
      }
    }
    public Std.Wrappers._IOption<RAST._IType> dtor_optType {
      get {
        var d = this;
        return ((Expr_DeclareVar)d)._optType;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_optRhs {
      get {
        var d = this;
        return ((Expr_DeclareVar)d)._optRhs;
      }
    }
    public RAST._IExpr dtor_cond {
      get {
        var d = this;
        return ((Expr_IfExpr)d)._cond;
      }
    }
    public RAST._IExpr dtor_thn {
      get {
        var d = this;
        return ((Expr_IfExpr)d)._thn;
      }
    }
    public RAST._IExpr dtor_els {
      get {
        var d = this;
        return ((Expr_IfExpr)d)._els;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_optCond {
      get {
        var d = this;
        return ((Expr_Loop)d)._optCond;
      }
    }
    public RAST._IExpr dtor_range {
      get {
        var d = this;
        return ((Expr_For)d)._range;
      }
    }
    public RAST._IExpr dtor_body {
      get {
        var d = this;
        return ((Expr_For)d)._body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_lbl {
      get {
        var d = this;
        return ((Expr_Labelled)d)._lbl;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_optLbl {
      get {
        var d = this;
        if (d is Expr_Break) { return ((Expr_Break)d)._optLbl; }
        return ((Expr_Continue)d)._optLbl;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_optExpr {
      get {
        var d = this;
        return ((Expr_Return)d)._optExpr;
      }
    }
    public RAST._IExpr dtor_obj {
      get {
        var d = this;
        if (d is Expr_Call) { return ((Expr_Call)d)._obj; }
        if (d is Expr_Select) { return ((Expr_Select)d)._obj; }
        return ((Expr_MemberSelect)d)._obj;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_typeParameters {
      get {
        var d = this;
        return ((Expr_Call)d)._typeParameters;
      }
    }
    public abstract _IExpr DowncastClone();
    public bool NoExtraSemicolonAfter() {
      return ((((((this).is_DeclareVar) || ((this).is_AssignVar)) || ((this).is_Break)) || ((this).is_Continue)) || ((this).is_Return)) || ((((this).is_RawExpr) && ((new BigInteger(((this).dtor_content).Count)).Sign == 1)) && ((((this).dtor_content).Select((new BigInteger(((this).dtor_content).Count)) - (BigInteger.One))) == (new Dafny.Rune(';'))));
    }
    public RAST._IExpr Optimize() {
      RAST._IExpr _source27 = this;
      if (_source27.is_RawExpr) {
        Dafny.ISequence<Dafny.Rune> _898___mcc_h0 = _source27.dtor_content;
        return this;
      } else if (_source27.is_Identifier) {
        Dafny.ISequence<Dafny.Rune> _899___mcc_h2 = _source27.dtor_name;
        return this;
      } else if (_source27.is_Match) {
        RAST._IExpr _900___mcc_h4 = _source27.dtor_matchee;
        Dafny.ISequence<RAST._IMatchCase> _901___mcc_h5 = _source27.dtor_cases;
        return this;
      } else if (_source27.is_StmtExpr) {
        RAST._IExpr _902___mcc_h8 = _source27.dtor_stmt;
        RAST._IExpr _903___mcc_h9 = _source27.dtor_rhs;
        return this;
      } else if (_source27.is_Block) {
        RAST._IExpr _904___mcc_h12 = _source27.dtor_underlying;
        return this;
      } else if (_source27.is_StructBuild) {
        Dafny.ISequence<Dafny.Rune> _905___mcc_h14 = _source27.dtor_name;
        Dafny.ISequence<RAST._IAssignIdentifier> _906___mcc_h15 = _source27.dtor_assignments;
        return this;
      } else if (_source27.is_Tuple) {
        Dafny.ISequence<RAST._IExpr> _907___mcc_h18 = _source27.dtor_arguments;
        return this;
      } else if (_source27.is_UnaryOp) {
        Dafny.ISequence<Dafny.Rune> _908___mcc_h20 = _source27.dtor_op1;
        RAST._IExpr _909___mcc_h21 = _source27.dtor_underlying;
        DAST.Format._IUnaryOpFormat _910___mcc_h22 = _source27.dtor_format;
        if (object.Equals(_908___mcc_h20, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
          RAST._IExpr _source28 = _909___mcc_h21;
          if (_source28.is_RawExpr) {
            Dafny.ISequence<Dafny.Rune> _911___mcc_h26 = _source28.dtor_content;
            return this;
          } else if (_source28.is_Identifier) {
            Dafny.ISequence<Dafny.Rune> _912___mcc_h28 = _source28.dtor_name;
            return this;
          } else if (_source28.is_Match) {
            RAST._IExpr _913___mcc_h30 = _source28.dtor_matchee;
            Dafny.ISequence<RAST._IMatchCase> _914___mcc_h31 = _source28.dtor_cases;
            return this;
          } else if (_source28.is_StmtExpr) {
            RAST._IExpr _915___mcc_h34 = _source28.dtor_stmt;
            RAST._IExpr _916___mcc_h35 = _source28.dtor_rhs;
            return this;
          } else if (_source28.is_Block) {
            RAST._IExpr _917___mcc_h38 = _source28.dtor_underlying;
            return this;
          } else if (_source28.is_StructBuild) {
            Dafny.ISequence<Dafny.Rune> _918___mcc_h40 = _source28.dtor_name;
            Dafny.ISequence<RAST._IAssignIdentifier> _919___mcc_h41 = _source28.dtor_assignments;
            return this;
          } else if (_source28.is_Tuple) {
            Dafny.ISequence<RAST._IExpr> _920___mcc_h44 = _source28.dtor_arguments;
            return this;
          } else if (_source28.is_UnaryOp) {
            Dafny.ISequence<Dafny.Rune> _921___mcc_h46 = _source28.dtor_op1;
            RAST._IExpr _922___mcc_h47 = _source28.dtor_underlying;
            DAST.Format._IUnaryOpFormat _923___mcc_h48 = _source28.dtor_format;
            return this;
          } else if (_source28.is_BinaryOp) {
            Dafny.ISequence<Dafny.Rune> _924___mcc_h52 = _source28.dtor_op2;
            RAST._IExpr _925___mcc_h53 = _source28.dtor_left;
            RAST._IExpr _926___mcc_h54 = _source28.dtor_right;
            DAST.Format._IBinaryOpFormat _927___mcc_h55 = _source28.dtor_format2;
            return this;
          } else if (_source28.is_TypeAscription) {
            RAST._IExpr _928___mcc_h60 = _source28.dtor_left;
            RAST._IType _929___mcc_h61 = _source28.dtor_tpe;
            return this;
          } else if (_source28.is_LiteralInt) {
            Dafny.ISequence<Dafny.Rune> _930___mcc_h64 = _source28.dtor_value;
            return this;
          } else if (_source28.is_LiteralString) {
            Dafny.ISequence<Dafny.Rune> _931___mcc_h66 = _source28.dtor_value;
            bool _932___mcc_h67 = _source28.dtor_binary;
            return this;
          } else if (_source28.is_ConversionNum) {
            RAST._IType _933___mcc_h70 = _source28.dtor_tpe;
            RAST._IExpr _934___mcc_h71 = _source28.dtor_underlying;
            return this;
          } else if (_source28.is_DeclareVar) {
            RAST._IDeclareType _935___mcc_h74 = _source28.dtor_declareType;
            Dafny.ISequence<Dafny.Rune> _936___mcc_h75 = _source28.dtor_name;
            Std.Wrappers._IOption<RAST._IType> _937___mcc_h76 = _source28.dtor_optType;
            Std.Wrappers._IOption<RAST._IExpr> _938___mcc_h77 = _source28.dtor_optRhs;
            return this;
          } else if (_source28.is_AssignVar) {
            Dafny.ISequence<Dafny.Rune> _939___mcc_h82 = _source28.dtor_name;
            RAST._IExpr _940___mcc_h83 = _source28.dtor_rhs;
            return this;
          } else if (_source28.is_IfExpr) {
            RAST._IExpr _941___mcc_h86 = _source28.dtor_cond;
            RAST._IExpr _942___mcc_h87 = _source28.dtor_thn;
            RAST._IExpr _943___mcc_h88 = _source28.dtor_els;
            return this;
          } else if (_source28.is_Loop) {
            Std.Wrappers._IOption<RAST._IExpr> _944___mcc_h92 = _source28.dtor_optCond;
            RAST._IExpr _945___mcc_h93 = _source28.dtor_underlying;
            return this;
          } else if (_source28.is_For) {
            Dafny.ISequence<Dafny.Rune> _946___mcc_h96 = _source28.dtor_name;
            RAST._IExpr _947___mcc_h97 = _source28.dtor_range;
            RAST._IExpr _948___mcc_h98 = _source28.dtor_body;
            return this;
          } else if (_source28.is_Labelled) {
            Dafny.ISequence<Dafny.Rune> _949___mcc_h102 = _source28.dtor_lbl;
            RAST._IExpr _950___mcc_h103 = _source28.dtor_underlying;
            return this;
          } else if (_source28.is_Break) {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _951___mcc_h106 = _source28.dtor_optLbl;
            return this;
          } else if (_source28.is_Continue) {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _952___mcc_h108 = _source28.dtor_optLbl;
            return this;
          } else if (_source28.is_Return) {
            Std.Wrappers._IOption<RAST._IExpr> _953___mcc_h110 = _source28.dtor_optExpr;
            return this;
          } else if (_source28.is_Call) {
            RAST._IExpr _954___mcc_h112 = _source28.dtor_obj;
            Dafny.ISequence<RAST._IType> _955___mcc_h113 = _source28.dtor_typeParameters;
            Dafny.ISequence<RAST._IExpr> _956___mcc_h114 = _source28.dtor_arguments;
            RAST._IExpr _source29 = _954___mcc_h112;
            if (_source29.is_RawExpr) {
              Dafny.ISequence<Dafny.Rune> _957___mcc_h118 = _source29.dtor_content;
              return this;
            } else if (_source29.is_Identifier) {
              Dafny.ISequence<Dafny.Rune> _958___mcc_h120 = _source29.dtor_name;
              return this;
            } else if (_source29.is_Match) {
              RAST._IExpr _959___mcc_h122 = _source29.dtor_matchee;
              Dafny.ISequence<RAST._IMatchCase> _960___mcc_h123 = _source29.dtor_cases;
              return this;
            } else if (_source29.is_StmtExpr) {
              RAST._IExpr _961___mcc_h126 = _source29.dtor_stmt;
              RAST._IExpr _962___mcc_h127 = _source29.dtor_rhs;
              return this;
            } else if (_source29.is_Block) {
              RAST._IExpr _963___mcc_h130 = _source29.dtor_underlying;
              return this;
            } else if (_source29.is_StructBuild) {
              Dafny.ISequence<Dafny.Rune> _964___mcc_h132 = _source29.dtor_name;
              Dafny.ISequence<RAST._IAssignIdentifier> _965___mcc_h133 = _source29.dtor_assignments;
              return this;
            } else if (_source29.is_Tuple) {
              Dafny.ISequence<RAST._IExpr> _966___mcc_h136 = _source29.dtor_arguments;
              return this;
            } else if (_source29.is_UnaryOp) {
              Dafny.ISequence<Dafny.Rune> _967___mcc_h138 = _source29.dtor_op1;
              RAST._IExpr _968___mcc_h139 = _source29.dtor_underlying;
              DAST.Format._IUnaryOpFormat _969___mcc_h140 = _source29.dtor_format;
              return this;
            } else if (_source29.is_BinaryOp) {
              Dafny.ISequence<Dafny.Rune> _970___mcc_h144 = _source29.dtor_op2;
              RAST._IExpr _971___mcc_h145 = _source29.dtor_left;
              RAST._IExpr _972___mcc_h146 = _source29.dtor_right;
              DAST.Format._IBinaryOpFormat _973___mcc_h147 = _source29.dtor_format2;
              return this;
            } else if (_source29.is_TypeAscription) {
              RAST._IExpr _974___mcc_h152 = _source29.dtor_left;
              RAST._IType _975___mcc_h153 = _source29.dtor_tpe;
              return this;
            } else if (_source29.is_LiteralInt) {
              Dafny.ISequence<Dafny.Rune> _976___mcc_h156 = _source29.dtor_value;
              return this;
            } else if (_source29.is_LiteralString) {
              Dafny.ISequence<Dafny.Rune> _977___mcc_h158 = _source29.dtor_value;
              bool _978___mcc_h159 = _source29.dtor_binary;
              return this;
            } else if (_source29.is_ConversionNum) {
              RAST._IType _979___mcc_h162 = _source29.dtor_tpe;
              RAST._IExpr _980___mcc_h163 = _source29.dtor_underlying;
              return this;
            } else if (_source29.is_DeclareVar) {
              RAST._IDeclareType _981___mcc_h166 = _source29.dtor_declareType;
              Dafny.ISequence<Dafny.Rune> _982___mcc_h167 = _source29.dtor_name;
              Std.Wrappers._IOption<RAST._IType> _983___mcc_h168 = _source29.dtor_optType;
              Std.Wrappers._IOption<RAST._IExpr> _984___mcc_h169 = _source29.dtor_optRhs;
              return this;
            } else if (_source29.is_AssignVar) {
              Dafny.ISequence<Dafny.Rune> _985___mcc_h174 = _source29.dtor_name;
              RAST._IExpr _986___mcc_h175 = _source29.dtor_rhs;
              return this;
            } else if (_source29.is_IfExpr) {
              RAST._IExpr _987___mcc_h178 = _source29.dtor_cond;
              RAST._IExpr _988___mcc_h179 = _source29.dtor_thn;
              RAST._IExpr _989___mcc_h180 = _source29.dtor_els;
              return this;
            } else if (_source29.is_Loop) {
              Std.Wrappers._IOption<RAST._IExpr> _990___mcc_h184 = _source29.dtor_optCond;
              RAST._IExpr _991___mcc_h185 = _source29.dtor_underlying;
              return this;
            } else if (_source29.is_For) {
              Dafny.ISequence<Dafny.Rune> _992___mcc_h188 = _source29.dtor_name;
              RAST._IExpr _993___mcc_h189 = _source29.dtor_range;
              RAST._IExpr _994___mcc_h190 = _source29.dtor_body;
              return this;
            } else if (_source29.is_Labelled) {
              Dafny.ISequence<Dafny.Rune> _995___mcc_h194 = _source29.dtor_lbl;
              RAST._IExpr _996___mcc_h195 = _source29.dtor_underlying;
              return this;
            } else if (_source29.is_Break) {
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _997___mcc_h198 = _source29.dtor_optLbl;
              return this;
            } else if (_source29.is_Continue) {
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _998___mcc_h200 = _source29.dtor_optLbl;
              return this;
            } else if (_source29.is_Return) {
              Std.Wrappers._IOption<RAST._IExpr> _999___mcc_h202 = _source29.dtor_optExpr;
              return this;
            } else if (_source29.is_Call) {
              RAST._IExpr _1000___mcc_h204 = _source29.dtor_obj;
              Dafny.ISequence<RAST._IType> _1001___mcc_h205 = _source29.dtor_typeParameters;
              Dafny.ISequence<RAST._IExpr> _1002___mcc_h206 = _source29.dtor_arguments;
              return this;
            } else if (_source29.is_Select) {
              RAST._IExpr _1003___mcc_h210 = _source29.dtor_obj;
              Dafny.ISequence<Dafny.Rune> _1004___mcc_h211 = _source29.dtor_name;
              if (object.Equals(_1004___mcc_h211, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                DAST.Format._IUnaryOpFormat _1005_format = _910___mcc_h22;
                Dafny.ISequence<RAST._IExpr> _1006_args = _956___mcc_h114;
                Dafny.ISequence<RAST._IType> _1007_typeArgs = _955___mcc_h113;
                RAST._IExpr _1008_underlying = _1003___mcc_h210;
                if (((_1007_typeArgs).Equals(Dafny.Sequence<RAST._IType>.FromElements())) && ((_1006_args).Equals(Dafny.Sequence<RAST._IExpr>.FromElements()))) {
                  return RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _1008_underlying, _1005_format);
                } else {
                  return this;
                }
              } else {
                return this;
              }
            } else {
              RAST._IExpr _1009___mcc_h214 = _source29.dtor_obj;
              Dafny.ISequence<Dafny.Rune> _1010___mcc_h215 = _source29.dtor_name;
              return this;
            }
          } else if (_source28.is_Select) {
            RAST._IExpr _1011___mcc_h218 = _source28.dtor_obj;
            Dafny.ISequence<Dafny.Rune> _1012___mcc_h219 = _source28.dtor_name;
            return this;
          } else {
            RAST._IExpr _1013___mcc_h222 = _source28.dtor_obj;
            Dafny.ISequence<Dafny.Rune> _1014___mcc_h223 = _source28.dtor_name;
            return this;
          }
        } else if (object.Equals(_908___mcc_h20, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"))) {
          RAST._IExpr _source30 = _909___mcc_h21;
          if (_source30.is_RawExpr) {
            Dafny.ISequence<Dafny.Rune> _1015___mcc_h226 = _source30.dtor_content;
            return this;
          } else if (_source30.is_Identifier) {
            Dafny.ISequence<Dafny.Rune> _1016___mcc_h228 = _source30.dtor_name;
            return this;
          } else if (_source30.is_Match) {
            RAST._IExpr _1017___mcc_h230 = _source30.dtor_matchee;
            Dafny.ISequence<RAST._IMatchCase> _1018___mcc_h231 = _source30.dtor_cases;
            return this;
          } else if (_source30.is_StmtExpr) {
            RAST._IExpr _1019___mcc_h234 = _source30.dtor_stmt;
            RAST._IExpr _1020___mcc_h235 = _source30.dtor_rhs;
            return this;
          } else if (_source30.is_Block) {
            RAST._IExpr _1021___mcc_h238 = _source30.dtor_underlying;
            return this;
          } else if (_source30.is_StructBuild) {
            Dafny.ISequence<Dafny.Rune> _1022___mcc_h240 = _source30.dtor_name;
            Dafny.ISequence<RAST._IAssignIdentifier> _1023___mcc_h241 = _source30.dtor_assignments;
            return this;
          } else if (_source30.is_Tuple) {
            Dafny.ISequence<RAST._IExpr> _1024___mcc_h244 = _source30.dtor_arguments;
            return this;
          } else if (_source30.is_UnaryOp) {
            Dafny.ISequence<Dafny.Rune> _1025___mcc_h246 = _source30.dtor_op1;
            RAST._IExpr _1026___mcc_h247 = _source30.dtor_underlying;
            DAST.Format._IUnaryOpFormat _1027___mcc_h248 = _source30.dtor_format;
            return this;
          } else if (_source30.is_BinaryOp) {
            Dafny.ISequence<Dafny.Rune> _1028___mcc_h252 = _source30.dtor_op2;
            RAST._IExpr _1029___mcc_h253 = _source30.dtor_left;
            RAST._IExpr _1030___mcc_h254 = _source30.dtor_right;
            DAST.Format._IBinaryOpFormat _1031___mcc_h255 = _source30.dtor_format2;
            if (object.Equals(_1028___mcc_h252, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
              DAST.Format._IUnaryOpFormat _source31 = _910___mcc_h22;
              if (_source31.is_NoFormat) {
                return this;
              } else {
                DAST.Format._IBinaryOpFormat _1032_format = _1031___mcc_h255;
                RAST._IExpr _1033_right = _1030___mcc_h254;
                RAST._IExpr _1034_left = _1029___mcc_h253;
                return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="), _1034_left, _1033_right, DAST.Format.BinaryOpFormat.create_NoFormat());
              }
            } else if (object.Equals(_1028___mcc_h252, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
              DAST.Format._IBinaryOpFormat _source32 = _1031___mcc_h255;
              if (_source32.is_NoFormat) {
                DAST.Format._IUnaryOpFormat _source33 = _910___mcc_h22;
                if (_source33.is_NoFormat) {
                  return this;
                } else {
                  RAST._IExpr _1035_right = _1030___mcc_h254;
                  RAST._IExpr _1036_left = _1029___mcc_h253;
                  return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="), _1036_left, _1035_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              } else if (_source32.is_ImpliesFormat) {
                return this;
              } else if (_source32.is_EquivalenceFormat) {
                return this;
              } else {
                DAST.Format._IUnaryOpFormat _source34 = _910___mcc_h22;
                if (_source34.is_NoFormat) {
                  return this;
                } else {
                  RAST._IExpr _1037_right = _1030___mcc_h254;
                  RAST._IExpr _1038_left = _1029___mcc_h253;
                  return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1037_right, _1038_left, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else {
              return this;
            }
          } else if (_source30.is_TypeAscription) {
            RAST._IExpr _1039___mcc_h260 = _source30.dtor_left;
            RAST._IType _1040___mcc_h261 = _source30.dtor_tpe;
            return this;
          } else if (_source30.is_LiteralInt) {
            Dafny.ISequence<Dafny.Rune> _1041___mcc_h264 = _source30.dtor_value;
            return this;
          } else if (_source30.is_LiteralString) {
            Dafny.ISequence<Dafny.Rune> _1042___mcc_h266 = _source30.dtor_value;
            bool _1043___mcc_h267 = _source30.dtor_binary;
            return this;
          } else if (_source30.is_ConversionNum) {
            RAST._IType _1044___mcc_h270 = _source30.dtor_tpe;
            RAST._IExpr _1045___mcc_h271 = _source30.dtor_underlying;
            return this;
          } else if (_source30.is_DeclareVar) {
            RAST._IDeclareType _1046___mcc_h274 = _source30.dtor_declareType;
            Dafny.ISequence<Dafny.Rune> _1047___mcc_h275 = _source30.dtor_name;
            Std.Wrappers._IOption<RAST._IType> _1048___mcc_h276 = _source30.dtor_optType;
            Std.Wrappers._IOption<RAST._IExpr> _1049___mcc_h277 = _source30.dtor_optRhs;
            return this;
          } else if (_source30.is_AssignVar) {
            Dafny.ISequence<Dafny.Rune> _1050___mcc_h282 = _source30.dtor_name;
            RAST._IExpr _1051___mcc_h283 = _source30.dtor_rhs;
            return this;
          } else if (_source30.is_IfExpr) {
            RAST._IExpr _1052___mcc_h286 = _source30.dtor_cond;
            RAST._IExpr _1053___mcc_h287 = _source30.dtor_thn;
            RAST._IExpr _1054___mcc_h288 = _source30.dtor_els;
            return this;
          } else if (_source30.is_Loop) {
            Std.Wrappers._IOption<RAST._IExpr> _1055___mcc_h292 = _source30.dtor_optCond;
            RAST._IExpr _1056___mcc_h293 = _source30.dtor_underlying;
            return this;
          } else if (_source30.is_For) {
            Dafny.ISequence<Dafny.Rune> _1057___mcc_h296 = _source30.dtor_name;
            RAST._IExpr _1058___mcc_h297 = _source30.dtor_range;
            RAST._IExpr _1059___mcc_h298 = _source30.dtor_body;
            return this;
          } else if (_source30.is_Labelled) {
            Dafny.ISequence<Dafny.Rune> _1060___mcc_h302 = _source30.dtor_lbl;
            RAST._IExpr _1061___mcc_h303 = _source30.dtor_underlying;
            return this;
          } else if (_source30.is_Break) {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1062___mcc_h306 = _source30.dtor_optLbl;
            return this;
          } else if (_source30.is_Continue) {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1063___mcc_h308 = _source30.dtor_optLbl;
            return this;
          } else if (_source30.is_Return) {
            Std.Wrappers._IOption<RAST._IExpr> _1064___mcc_h310 = _source30.dtor_optExpr;
            return this;
          } else if (_source30.is_Call) {
            RAST._IExpr _1065___mcc_h312 = _source30.dtor_obj;
            Dafny.ISequence<RAST._IType> _1066___mcc_h313 = _source30.dtor_typeParameters;
            Dafny.ISequence<RAST._IExpr> _1067___mcc_h314 = _source30.dtor_arguments;
            return this;
          } else if (_source30.is_Select) {
            RAST._IExpr _1068___mcc_h318 = _source30.dtor_obj;
            Dafny.ISequence<Dafny.Rune> _1069___mcc_h319 = _source30.dtor_name;
            return this;
          } else {
            RAST._IExpr _1070___mcc_h322 = _source30.dtor_obj;
            Dafny.ISequence<Dafny.Rune> _1071___mcc_h323 = _source30.dtor_name;
            return this;
          }
        } else {
          return this;
        }
      } else if (_source27.is_BinaryOp) {
        Dafny.ISequence<Dafny.Rune> _1072___mcc_h326 = _source27.dtor_op2;
        RAST._IExpr _1073___mcc_h327 = _source27.dtor_left;
        RAST._IExpr _1074___mcc_h328 = _source27.dtor_right;
        DAST.Format._IBinaryOpFormat _1075___mcc_h329 = _source27.dtor_format2;
        return this;
      } else if (_source27.is_TypeAscription) {
        RAST._IExpr _1076___mcc_h334 = _source27.dtor_left;
        RAST._IType _1077___mcc_h335 = _source27.dtor_tpe;
        return this;
      } else if (_source27.is_LiteralInt) {
        Dafny.ISequence<Dafny.Rune> _1078___mcc_h338 = _source27.dtor_value;
        return this;
      } else if (_source27.is_LiteralString) {
        Dafny.ISequence<Dafny.Rune> _1079___mcc_h340 = _source27.dtor_value;
        bool _1080___mcc_h341 = _source27.dtor_binary;
        return this;
      } else if (_source27.is_ConversionNum) {
        RAST._IType _1081___mcc_h344 = _source27.dtor_tpe;
        RAST._IExpr _1082___mcc_h345 = _source27.dtor_underlying;
        RAST._IExpr _1083_expr = _1082___mcc_h345;
        RAST._IType _1084_tpe = _1081___mcc_h344;
        if (((((((((((_1084_tpe).is_U8) || ((_1084_tpe).is_U16)) || ((_1084_tpe).is_U32)) || ((_1084_tpe).is_U64)) || ((_1084_tpe).is_U128)) || ((_1084_tpe).is_I8)) || ((_1084_tpe).is_I16)) || ((_1084_tpe).is_I32)) || ((_1084_tpe).is_I64)) || ((_1084_tpe).is_I128)) {
          RAST._IExpr _source35 = _1083_expr;
          if (_source35.is_RawExpr) {
            Dafny.ISequence<Dafny.Rune> _1085___mcc_h400 = _source35.dtor_content;
            return this;
          } else if (_source35.is_Identifier) {
            Dafny.ISequence<Dafny.Rune> _1086___mcc_h402 = _source35.dtor_name;
            return this;
          } else if (_source35.is_Match) {
            RAST._IExpr _1087___mcc_h404 = _source35.dtor_matchee;
            Dafny.ISequence<RAST._IMatchCase> _1088___mcc_h405 = _source35.dtor_cases;
            return this;
          } else if (_source35.is_StmtExpr) {
            RAST._IExpr _1089___mcc_h408 = _source35.dtor_stmt;
            RAST._IExpr _1090___mcc_h409 = _source35.dtor_rhs;
            return this;
          } else if (_source35.is_Block) {
            RAST._IExpr _1091___mcc_h412 = _source35.dtor_underlying;
            return this;
          } else if (_source35.is_StructBuild) {
            Dafny.ISequence<Dafny.Rune> _1092___mcc_h414 = _source35.dtor_name;
            Dafny.ISequence<RAST._IAssignIdentifier> _1093___mcc_h415 = _source35.dtor_assignments;
            return this;
          } else if (_source35.is_Tuple) {
            Dafny.ISequence<RAST._IExpr> _1094___mcc_h418 = _source35.dtor_arguments;
            return this;
          } else if (_source35.is_UnaryOp) {
            Dafny.ISequence<Dafny.Rune> _1095___mcc_h420 = _source35.dtor_op1;
            RAST._IExpr _1096___mcc_h421 = _source35.dtor_underlying;
            DAST.Format._IUnaryOpFormat _1097___mcc_h422 = _source35.dtor_format;
            return this;
          } else if (_source35.is_BinaryOp) {
            Dafny.ISequence<Dafny.Rune> _1098___mcc_h426 = _source35.dtor_op2;
            RAST._IExpr _1099___mcc_h427 = _source35.dtor_left;
            RAST._IExpr _1100___mcc_h428 = _source35.dtor_right;
            DAST.Format._IBinaryOpFormat _1101___mcc_h429 = _source35.dtor_format2;
            return this;
          } else if (_source35.is_TypeAscription) {
            RAST._IExpr _1102___mcc_h434 = _source35.dtor_left;
            RAST._IType _1103___mcc_h435 = _source35.dtor_tpe;
            return this;
          } else if (_source35.is_LiteralInt) {
            Dafny.ISequence<Dafny.Rune> _1104___mcc_h438 = _source35.dtor_value;
            return this;
          } else if (_source35.is_LiteralString) {
            Dafny.ISequence<Dafny.Rune> _1105___mcc_h440 = _source35.dtor_value;
            bool _1106___mcc_h441 = _source35.dtor_binary;
            return this;
          } else if (_source35.is_ConversionNum) {
            RAST._IType _1107___mcc_h444 = _source35.dtor_tpe;
            RAST._IExpr _1108___mcc_h445 = _source35.dtor_underlying;
            return this;
          } else if (_source35.is_DeclareVar) {
            RAST._IDeclareType _1109___mcc_h448 = _source35.dtor_declareType;
            Dafny.ISequence<Dafny.Rune> _1110___mcc_h449 = _source35.dtor_name;
            Std.Wrappers._IOption<RAST._IType> _1111___mcc_h450 = _source35.dtor_optType;
            Std.Wrappers._IOption<RAST._IExpr> _1112___mcc_h451 = _source35.dtor_optRhs;
            return this;
          } else if (_source35.is_AssignVar) {
            Dafny.ISequence<Dafny.Rune> _1113___mcc_h456 = _source35.dtor_name;
            RAST._IExpr _1114___mcc_h457 = _source35.dtor_rhs;
            return this;
          } else if (_source35.is_IfExpr) {
            RAST._IExpr _1115___mcc_h460 = _source35.dtor_cond;
            RAST._IExpr _1116___mcc_h461 = _source35.dtor_thn;
            RAST._IExpr _1117___mcc_h462 = _source35.dtor_els;
            return this;
          } else if (_source35.is_Loop) {
            Std.Wrappers._IOption<RAST._IExpr> _1118___mcc_h466 = _source35.dtor_optCond;
            RAST._IExpr _1119___mcc_h467 = _source35.dtor_underlying;
            return this;
          } else if (_source35.is_For) {
            Dafny.ISequence<Dafny.Rune> _1120___mcc_h470 = _source35.dtor_name;
            RAST._IExpr _1121___mcc_h471 = _source35.dtor_range;
            RAST._IExpr _1122___mcc_h472 = _source35.dtor_body;
            return this;
          } else if (_source35.is_Labelled) {
            Dafny.ISequence<Dafny.Rune> _1123___mcc_h476 = _source35.dtor_lbl;
            RAST._IExpr _1124___mcc_h477 = _source35.dtor_underlying;
            return this;
          } else if (_source35.is_Break) {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1125___mcc_h480 = _source35.dtor_optLbl;
            return this;
          } else if (_source35.is_Continue) {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1126___mcc_h482 = _source35.dtor_optLbl;
            return this;
          } else if (_source35.is_Return) {
            Std.Wrappers._IOption<RAST._IExpr> _1127___mcc_h484 = _source35.dtor_optExpr;
            return this;
          } else if (_source35.is_Call) {
            RAST._IExpr _1128___mcc_h486 = _source35.dtor_obj;
            Dafny.ISequence<RAST._IType> _1129___mcc_h487 = _source35.dtor_typeParameters;
            Dafny.ISequence<RAST._IExpr> _1130___mcc_h488 = _source35.dtor_arguments;
            RAST._IExpr _source36 = _1128___mcc_h486;
            if (_source36.is_RawExpr) {
              Dafny.ISequence<Dafny.Rune> _1131___mcc_h492 = _source36.dtor_content;
              return this;
            } else if (_source36.is_Identifier) {
              Dafny.ISequence<Dafny.Rune> _1132___mcc_h494 = _source36.dtor_name;
              return this;
            } else if (_source36.is_Match) {
              RAST._IExpr _1133___mcc_h496 = _source36.dtor_matchee;
              Dafny.ISequence<RAST._IMatchCase> _1134___mcc_h497 = _source36.dtor_cases;
              return this;
            } else if (_source36.is_StmtExpr) {
              RAST._IExpr _1135___mcc_h500 = _source36.dtor_stmt;
              RAST._IExpr _1136___mcc_h501 = _source36.dtor_rhs;
              return this;
            } else if (_source36.is_Block) {
              RAST._IExpr _1137___mcc_h504 = _source36.dtor_underlying;
              return this;
            } else if (_source36.is_StructBuild) {
              Dafny.ISequence<Dafny.Rune> _1138___mcc_h506 = _source36.dtor_name;
              Dafny.ISequence<RAST._IAssignIdentifier> _1139___mcc_h507 = _source36.dtor_assignments;
              return this;
            } else if (_source36.is_Tuple) {
              Dafny.ISequence<RAST._IExpr> _1140___mcc_h510 = _source36.dtor_arguments;
              return this;
            } else if (_source36.is_UnaryOp) {
              Dafny.ISequence<Dafny.Rune> _1141___mcc_h512 = _source36.dtor_op1;
              RAST._IExpr _1142___mcc_h513 = _source36.dtor_underlying;
              DAST.Format._IUnaryOpFormat _1143___mcc_h514 = _source36.dtor_format;
              return this;
            } else if (_source36.is_BinaryOp) {
              Dafny.ISequence<Dafny.Rune> _1144___mcc_h518 = _source36.dtor_op2;
              RAST._IExpr _1145___mcc_h519 = _source36.dtor_left;
              RAST._IExpr _1146___mcc_h520 = _source36.dtor_right;
              DAST.Format._IBinaryOpFormat _1147___mcc_h521 = _source36.dtor_format2;
              return this;
            } else if (_source36.is_TypeAscription) {
              RAST._IExpr _1148___mcc_h526 = _source36.dtor_left;
              RAST._IType _1149___mcc_h527 = _source36.dtor_tpe;
              return this;
            } else if (_source36.is_LiteralInt) {
              Dafny.ISequence<Dafny.Rune> _1150___mcc_h530 = _source36.dtor_value;
              return this;
            } else if (_source36.is_LiteralString) {
              Dafny.ISequence<Dafny.Rune> _1151___mcc_h532 = _source36.dtor_value;
              bool _1152___mcc_h533 = _source36.dtor_binary;
              return this;
            } else if (_source36.is_ConversionNum) {
              RAST._IType _1153___mcc_h536 = _source36.dtor_tpe;
              RAST._IExpr _1154___mcc_h537 = _source36.dtor_underlying;
              return this;
            } else if (_source36.is_DeclareVar) {
              RAST._IDeclareType _1155___mcc_h540 = _source36.dtor_declareType;
              Dafny.ISequence<Dafny.Rune> _1156___mcc_h541 = _source36.dtor_name;
              Std.Wrappers._IOption<RAST._IType> _1157___mcc_h542 = _source36.dtor_optType;
              Std.Wrappers._IOption<RAST._IExpr> _1158___mcc_h543 = _source36.dtor_optRhs;
              return this;
            } else if (_source36.is_AssignVar) {
              Dafny.ISequence<Dafny.Rune> _1159___mcc_h548 = _source36.dtor_name;
              RAST._IExpr _1160___mcc_h549 = _source36.dtor_rhs;
              return this;
            } else if (_source36.is_IfExpr) {
              RAST._IExpr _1161___mcc_h552 = _source36.dtor_cond;
              RAST._IExpr _1162___mcc_h553 = _source36.dtor_thn;
              RAST._IExpr _1163___mcc_h554 = _source36.dtor_els;
              return this;
            } else if (_source36.is_Loop) {
              Std.Wrappers._IOption<RAST._IExpr> _1164___mcc_h558 = _source36.dtor_optCond;
              RAST._IExpr _1165___mcc_h559 = _source36.dtor_underlying;
              return this;
            } else if (_source36.is_For) {
              Dafny.ISequence<Dafny.Rune> _1166___mcc_h562 = _source36.dtor_name;
              RAST._IExpr _1167___mcc_h563 = _source36.dtor_range;
              RAST._IExpr _1168___mcc_h564 = _source36.dtor_body;
              return this;
            } else if (_source36.is_Labelled) {
              Dafny.ISequence<Dafny.Rune> _1169___mcc_h568 = _source36.dtor_lbl;
              RAST._IExpr _1170___mcc_h569 = _source36.dtor_underlying;
              return this;
            } else if (_source36.is_Break) {
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1171___mcc_h572 = _source36.dtor_optLbl;
              return this;
            } else if (_source36.is_Continue) {
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1172___mcc_h574 = _source36.dtor_optLbl;
              return this;
            } else if (_source36.is_Return) {
              Std.Wrappers._IOption<RAST._IExpr> _1173___mcc_h576 = _source36.dtor_optExpr;
              return this;
            } else if (_source36.is_Call) {
              RAST._IExpr _1174___mcc_h578 = _source36.dtor_obj;
              Dafny.ISequence<RAST._IType> _1175___mcc_h579 = _source36.dtor_typeParameters;
              Dafny.ISequence<RAST._IExpr> _1176___mcc_h580 = _source36.dtor_arguments;
              return this;
            } else if (_source36.is_Select) {
              RAST._IExpr _1177___mcc_h584 = _source36.dtor_obj;
              Dafny.ISequence<Dafny.Rune> _1178___mcc_h585 = _source36.dtor_name;
              return this;
            } else {
              RAST._IExpr _1179___mcc_h588 = _source36.dtor_obj;
              Dafny.ISequence<Dafny.Rune> _1180___mcc_h589 = _source36.dtor_name;
              RAST._IExpr _source37 = _1179___mcc_h588;
              if (_source37.is_RawExpr) {
                Dafny.ISequence<Dafny.Rune> _1181___mcc_h592 = _source37.dtor_content;
                return this;
              } else if (_source37.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> _1182___mcc_h594 = _source37.dtor_name;
                return this;
              } else if (_source37.is_Match) {
                RAST._IExpr _1183___mcc_h596 = _source37.dtor_matchee;
                Dafny.ISequence<RAST._IMatchCase> _1184___mcc_h597 = _source37.dtor_cases;
                return this;
              } else if (_source37.is_StmtExpr) {
                RAST._IExpr _1185___mcc_h600 = _source37.dtor_stmt;
                RAST._IExpr _1186___mcc_h601 = _source37.dtor_rhs;
                return this;
              } else if (_source37.is_Block) {
                RAST._IExpr _1187___mcc_h604 = _source37.dtor_underlying;
                return this;
              } else if (_source37.is_StructBuild) {
                Dafny.ISequence<Dafny.Rune> _1188___mcc_h606 = _source37.dtor_name;
                Dafny.ISequence<RAST._IAssignIdentifier> _1189___mcc_h607 = _source37.dtor_assignments;
                return this;
              } else if (_source37.is_Tuple) {
                Dafny.ISequence<RAST._IExpr> _1190___mcc_h610 = _source37.dtor_arguments;
                return this;
              } else if (_source37.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> _1191___mcc_h612 = _source37.dtor_op1;
                RAST._IExpr _1192___mcc_h613 = _source37.dtor_underlying;
                DAST.Format._IUnaryOpFormat _1193___mcc_h614 = _source37.dtor_format;
                return this;
              } else if (_source37.is_BinaryOp) {
                Dafny.ISequence<Dafny.Rune> _1194___mcc_h618 = _source37.dtor_op2;
                RAST._IExpr _1195___mcc_h619 = _source37.dtor_left;
                RAST._IExpr _1196___mcc_h620 = _source37.dtor_right;
                DAST.Format._IBinaryOpFormat _1197___mcc_h621 = _source37.dtor_format2;
                return this;
              } else if (_source37.is_TypeAscription) {
                RAST._IExpr _1198___mcc_h626 = _source37.dtor_left;
                RAST._IType _1199___mcc_h627 = _source37.dtor_tpe;
                return this;
              } else if (_source37.is_LiteralInt) {
                Dafny.ISequence<Dafny.Rune> _1200___mcc_h630 = _source37.dtor_value;
                return this;
              } else if (_source37.is_LiteralString) {
                Dafny.ISequence<Dafny.Rune> _1201___mcc_h632 = _source37.dtor_value;
                bool _1202___mcc_h633 = _source37.dtor_binary;
                return this;
              } else if (_source37.is_ConversionNum) {
                RAST._IType _1203___mcc_h636 = _source37.dtor_tpe;
                RAST._IExpr _1204___mcc_h637 = _source37.dtor_underlying;
                return this;
              } else if (_source37.is_DeclareVar) {
                RAST._IDeclareType _1205___mcc_h640 = _source37.dtor_declareType;
                Dafny.ISequence<Dafny.Rune> _1206___mcc_h641 = _source37.dtor_name;
                Std.Wrappers._IOption<RAST._IType> _1207___mcc_h642 = _source37.dtor_optType;
                Std.Wrappers._IOption<RAST._IExpr> _1208___mcc_h643 = _source37.dtor_optRhs;
                return this;
              } else if (_source37.is_AssignVar) {
                Dafny.ISequence<Dafny.Rune> _1209___mcc_h648 = _source37.dtor_name;
                RAST._IExpr _1210___mcc_h649 = _source37.dtor_rhs;
                return this;
              } else if (_source37.is_IfExpr) {
                RAST._IExpr _1211___mcc_h652 = _source37.dtor_cond;
                RAST._IExpr _1212___mcc_h653 = _source37.dtor_thn;
                RAST._IExpr _1213___mcc_h654 = _source37.dtor_els;
                return this;
              } else if (_source37.is_Loop) {
                Std.Wrappers._IOption<RAST._IExpr> _1214___mcc_h658 = _source37.dtor_optCond;
                RAST._IExpr _1215___mcc_h659 = _source37.dtor_underlying;
                return this;
              } else if (_source37.is_For) {
                Dafny.ISequence<Dafny.Rune> _1216___mcc_h662 = _source37.dtor_name;
                RAST._IExpr _1217___mcc_h663 = _source37.dtor_range;
                RAST._IExpr _1218___mcc_h664 = _source37.dtor_body;
                return this;
              } else if (_source37.is_Labelled) {
                Dafny.ISequence<Dafny.Rune> _1219___mcc_h668 = _source37.dtor_lbl;
                RAST._IExpr _1220___mcc_h669 = _source37.dtor_underlying;
                return this;
              } else if (_source37.is_Break) {
                Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1221___mcc_h672 = _source37.dtor_optLbl;
                return this;
              } else if (_source37.is_Continue) {
                Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1222___mcc_h674 = _source37.dtor_optLbl;
                return this;
              } else if (_source37.is_Return) {
                Std.Wrappers._IOption<RAST._IExpr> _1223___mcc_h676 = _source37.dtor_optExpr;
                return this;
              } else if (_source37.is_Call) {
                RAST._IExpr _1224___mcc_h678 = _source37.dtor_obj;
                Dafny.ISequence<RAST._IType> _1225___mcc_h679 = _source37.dtor_typeParameters;
                Dafny.ISequence<RAST._IExpr> _1226___mcc_h680 = _source37.dtor_arguments;
                return this;
              } else if (_source37.is_Select) {
                RAST._IExpr _1227___mcc_h684 = _source37.dtor_obj;
                Dafny.ISequence<Dafny.Rune> _1228___mcc_h685 = _source37.dtor_name;
                return this;
              } else {
                RAST._IExpr _1229___mcc_h688 = _source37.dtor_obj;
                Dafny.ISequence<Dafny.Rune> _1230___mcc_h689 = _source37.dtor_name;
                RAST._IExpr _source38 = _1229___mcc_h688;
                if (_source38.is_RawExpr) {
                  Dafny.ISequence<Dafny.Rune> _1231___mcc_h692 = _source38.dtor_content;
                  return this;
                } else if (_source38.is_Identifier) {
                  Dafny.ISequence<Dafny.Rune> _1232___mcc_h694 = _source38.dtor_name;
                  return this;
                } else if (_source38.is_Match) {
                  RAST._IExpr _1233___mcc_h696 = _source38.dtor_matchee;
                  Dafny.ISequence<RAST._IMatchCase> _1234___mcc_h697 = _source38.dtor_cases;
                  return this;
                } else if (_source38.is_StmtExpr) {
                  RAST._IExpr _1235___mcc_h700 = _source38.dtor_stmt;
                  RAST._IExpr _1236___mcc_h701 = _source38.dtor_rhs;
                  return this;
                } else if (_source38.is_Block) {
                  RAST._IExpr _1237___mcc_h704 = _source38.dtor_underlying;
                  return this;
                } else if (_source38.is_StructBuild) {
                  Dafny.ISequence<Dafny.Rune> _1238___mcc_h706 = _source38.dtor_name;
                  Dafny.ISequence<RAST._IAssignIdentifier> _1239___mcc_h707 = _source38.dtor_assignments;
                  return this;
                } else if (_source38.is_Tuple) {
                  Dafny.ISequence<RAST._IExpr> _1240___mcc_h710 = _source38.dtor_arguments;
                  return this;
                } else if (_source38.is_UnaryOp) {
                  Dafny.ISequence<Dafny.Rune> _1241___mcc_h712 = _source38.dtor_op1;
                  RAST._IExpr _1242___mcc_h713 = _source38.dtor_underlying;
                  DAST.Format._IUnaryOpFormat _1243___mcc_h714 = _source38.dtor_format;
                  return this;
                } else if (_source38.is_BinaryOp) {
                  Dafny.ISequence<Dafny.Rune> _1244___mcc_h718 = _source38.dtor_op2;
                  RAST._IExpr _1245___mcc_h719 = _source38.dtor_left;
                  RAST._IExpr _1246___mcc_h720 = _source38.dtor_right;
                  DAST.Format._IBinaryOpFormat _1247___mcc_h721 = _source38.dtor_format2;
                  return this;
                } else if (_source38.is_TypeAscription) {
                  RAST._IExpr _1248___mcc_h726 = _source38.dtor_left;
                  RAST._IType _1249___mcc_h727 = _source38.dtor_tpe;
                  return this;
                } else if (_source38.is_LiteralInt) {
                  Dafny.ISequence<Dafny.Rune> _1250___mcc_h730 = _source38.dtor_value;
                  return this;
                } else if (_source38.is_LiteralString) {
                  Dafny.ISequence<Dafny.Rune> _1251___mcc_h732 = _source38.dtor_value;
                  bool _1252___mcc_h733 = _source38.dtor_binary;
                  return this;
                } else if (_source38.is_ConversionNum) {
                  RAST._IType _1253___mcc_h736 = _source38.dtor_tpe;
                  RAST._IExpr _1254___mcc_h737 = _source38.dtor_underlying;
                  return this;
                } else if (_source38.is_DeclareVar) {
                  RAST._IDeclareType _1255___mcc_h740 = _source38.dtor_declareType;
                  Dafny.ISequence<Dafny.Rune> _1256___mcc_h741 = _source38.dtor_name;
                  Std.Wrappers._IOption<RAST._IType> _1257___mcc_h742 = _source38.dtor_optType;
                  Std.Wrappers._IOption<RAST._IExpr> _1258___mcc_h743 = _source38.dtor_optRhs;
                  return this;
                } else if (_source38.is_AssignVar) {
                  Dafny.ISequence<Dafny.Rune> _1259___mcc_h748 = _source38.dtor_name;
                  RAST._IExpr _1260___mcc_h749 = _source38.dtor_rhs;
                  return this;
                } else if (_source38.is_IfExpr) {
                  RAST._IExpr _1261___mcc_h752 = _source38.dtor_cond;
                  RAST._IExpr _1262___mcc_h753 = _source38.dtor_thn;
                  RAST._IExpr _1263___mcc_h754 = _source38.dtor_els;
                  return this;
                } else if (_source38.is_Loop) {
                  Std.Wrappers._IOption<RAST._IExpr> _1264___mcc_h758 = _source38.dtor_optCond;
                  RAST._IExpr _1265___mcc_h759 = _source38.dtor_underlying;
                  return this;
                } else if (_source38.is_For) {
                  Dafny.ISequence<Dafny.Rune> _1266___mcc_h762 = _source38.dtor_name;
                  RAST._IExpr _1267___mcc_h763 = _source38.dtor_range;
                  RAST._IExpr _1268___mcc_h764 = _source38.dtor_body;
                  return this;
                } else if (_source38.is_Labelled) {
                  Dafny.ISequence<Dafny.Rune> _1269___mcc_h768 = _source38.dtor_lbl;
                  RAST._IExpr _1270___mcc_h769 = _source38.dtor_underlying;
                  return this;
                } else if (_source38.is_Break) {
                  Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1271___mcc_h772 = _source38.dtor_optLbl;
                  return this;
                } else if (_source38.is_Continue) {
                  Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1272___mcc_h774 = _source38.dtor_optLbl;
                  return this;
                } else if (_source38.is_Return) {
                  Std.Wrappers._IOption<RAST._IExpr> _1273___mcc_h776 = _source38.dtor_optExpr;
                  return this;
                } else if (_source38.is_Call) {
                  RAST._IExpr _1274___mcc_h778 = _source38.dtor_obj;
                  Dafny.ISequence<RAST._IType> _1275___mcc_h779 = _source38.dtor_typeParameters;
                  Dafny.ISequence<RAST._IExpr> _1276___mcc_h780 = _source38.dtor_arguments;
                  return this;
                } else if (_source38.is_Select) {
                  RAST._IExpr _1277___mcc_h784 = _source38.dtor_obj;
                  Dafny.ISequence<Dafny.Rune> _1278___mcc_h785 = _source38.dtor_name;
                  return this;
                } else {
                  RAST._IExpr _1279___mcc_h788 = _source38.dtor_obj;
                  Dafny.ISequence<Dafny.Rune> _1280___mcc_h789 = _source38.dtor_name;
                  RAST._IExpr _source39 = _1279___mcc_h788;
                  if (_source39.is_RawExpr) {
                    Dafny.ISequence<Dafny.Rune> _1281___mcc_h792 = _source39.dtor_content;
                    return this;
                  } else if (_source39.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> _1282___mcc_h794 = _source39.dtor_name;
                    if (object.Equals(_1282___mcc_h794, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                      if (object.Equals(_1280___mcc_h789, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime"))) {
                        if (object.Equals(_1230___mcc_h689, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))) {
                          if (object.Equals(_1180___mcc_h589, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))) {
                            Dafny.ISequence<RAST._IExpr> _1283_args = _1130___mcc_h488;
                            Dafny.ISequence<RAST._IType> _1284_tpe = _1129___mcc_h487;
                            if (((new BigInteger((_1284_tpe).Count)).Sign == 0) && ((new BigInteger((_1283_args).Count)) == (BigInteger.One))) {
                              RAST._IExpr _source40 = (_1283_args).Select(BigInteger.Zero);
                              if (_source40.is_RawExpr) {
                                Dafny.ISequence<Dafny.Rune> _1285___mcc_h900 = _source40.dtor_content;
                                return this;
                              } else if (_source40.is_Identifier) {
                                Dafny.ISequence<Dafny.Rune> _1286___mcc_h902 = _source40.dtor_name;
                                return this;
                              } else if (_source40.is_Match) {
                                RAST._IExpr _1287___mcc_h904 = _source40.dtor_matchee;
                                Dafny.ISequence<RAST._IMatchCase> _1288___mcc_h905 = _source40.dtor_cases;
                                return this;
                              } else if (_source40.is_StmtExpr) {
                                RAST._IExpr _1289___mcc_h908 = _source40.dtor_stmt;
                                RAST._IExpr _1290___mcc_h909 = _source40.dtor_rhs;
                                return this;
                              } else if (_source40.is_Block) {
                                RAST._IExpr _1291___mcc_h912 = _source40.dtor_underlying;
                                return this;
                              } else if (_source40.is_StructBuild) {
                                Dafny.ISequence<Dafny.Rune> _1292___mcc_h914 = _source40.dtor_name;
                                Dafny.ISequence<RAST._IAssignIdentifier> _1293___mcc_h915 = _source40.dtor_assignments;
                                return this;
                              } else if (_source40.is_Tuple) {
                                Dafny.ISequence<RAST._IExpr> _1294___mcc_h918 = _source40.dtor_arguments;
                                return this;
                              } else if (_source40.is_UnaryOp) {
                                Dafny.ISequence<Dafny.Rune> _1295___mcc_h920 = _source40.dtor_op1;
                                RAST._IExpr _1296___mcc_h921 = _source40.dtor_underlying;
                                DAST.Format._IUnaryOpFormat _1297___mcc_h922 = _source40.dtor_format;
                                return this;
                              } else if (_source40.is_BinaryOp) {
                                Dafny.ISequence<Dafny.Rune> _1298___mcc_h926 = _source40.dtor_op2;
                                RAST._IExpr _1299___mcc_h927 = _source40.dtor_left;
                                RAST._IExpr _1300___mcc_h928 = _source40.dtor_right;
                                DAST.Format._IBinaryOpFormat _1301___mcc_h929 = _source40.dtor_format2;
                                return this;
                              } else if (_source40.is_TypeAscription) {
                                RAST._IExpr _1302___mcc_h934 = _source40.dtor_left;
                                RAST._IType _1303___mcc_h935 = _source40.dtor_tpe;
                                return this;
                              } else if (_source40.is_LiteralInt) {
                                Dafny.ISequence<Dafny.Rune> _1304___mcc_h938 = _source40.dtor_value;
                                Dafny.ISequence<Dafny.Rune> _1305_number = _1304___mcc_h938;
                                return RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/*optimized*/"), _1305_number));
                              } else if (_source40.is_LiteralString) {
                                Dafny.ISequence<Dafny.Rune> _1306___mcc_h940 = _source40.dtor_value;
                                bool _1307___mcc_h941 = _source40.dtor_binary;
                                Dafny.ISequence<Dafny.Rune> _1308_number = _1306___mcc_h940;
                                return RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/*optimized*/"), _1308_number));
                              } else if (_source40.is_ConversionNum) {
                                RAST._IType _1309___mcc_h944 = _source40.dtor_tpe;
                                RAST._IExpr _1310___mcc_h945 = _source40.dtor_underlying;
                                return this;
                              } else if (_source40.is_DeclareVar) {
                                RAST._IDeclareType _1311___mcc_h948 = _source40.dtor_declareType;
                                Dafny.ISequence<Dafny.Rune> _1312___mcc_h949 = _source40.dtor_name;
                                Std.Wrappers._IOption<RAST._IType> _1313___mcc_h950 = _source40.dtor_optType;
                                Std.Wrappers._IOption<RAST._IExpr> _1314___mcc_h951 = _source40.dtor_optRhs;
                                return this;
                              } else if (_source40.is_AssignVar) {
                                Dafny.ISequence<Dafny.Rune> _1315___mcc_h956 = _source40.dtor_name;
                                RAST._IExpr _1316___mcc_h957 = _source40.dtor_rhs;
                                return this;
                              } else if (_source40.is_IfExpr) {
                                RAST._IExpr _1317___mcc_h960 = _source40.dtor_cond;
                                RAST._IExpr _1318___mcc_h961 = _source40.dtor_thn;
                                RAST._IExpr _1319___mcc_h962 = _source40.dtor_els;
                                return this;
                              } else if (_source40.is_Loop) {
                                Std.Wrappers._IOption<RAST._IExpr> _1320___mcc_h966 = _source40.dtor_optCond;
                                RAST._IExpr _1321___mcc_h967 = _source40.dtor_underlying;
                                return this;
                              } else if (_source40.is_For) {
                                Dafny.ISequence<Dafny.Rune> _1322___mcc_h970 = _source40.dtor_name;
                                RAST._IExpr _1323___mcc_h971 = _source40.dtor_range;
                                RAST._IExpr _1324___mcc_h972 = _source40.dtor_body;
                                return this;
                              } else if (_source40.is_Labelled) {
                                Dafny.ISequence<Dafny.Rune> _1325___mcc_h976 = _source40.dtor_lbl;
                                RAST._IExpr _1326___mcc_h977 = _source40.dtor_underlying;
                                return this;
                              } else if (_source40.is_Break) {
                                Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1327___mcc_h980 = _source40.dtor_optLbl;
                                return this;
                              } else if (_source40.is_Continue) {
                                Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1328___mcc_h982 = _source40.dtor_optLbl;
                                return this;
                              } else if (_source40.is_Return) {
                                Std.Wrappers._IOption<RAST._IExpr> _1329___mcc_h984 = _source40.dtor_optExpr;
                                return this;
                              } else if (_source40.is_Call) {
                                RAST._IExpr _1330___mcc_h986 = _source40.dtor_obj;
                                Dafny.ISequence<RAST._IType> _1331___mcc_h987 = _source40.dtor_typeParameters;
                                Dafny.ISequence<RAST._IExpr> _1332___mcc_h988 = _source40.dtor_arguments;
                                return this;
                              } else if (_source40.is_Select) {
                                RAST._IExpr _1333___mcc_h992 = _source40.dtor_obj;
                                Dafny.ISequence<Dafny.Rune> _1334___mcc_h993 = _source40.dtor_name;
                                return this;
                              } else {
                                RAST._IExpr _1335___mcc_h996 = _source40.dtor_obj;
                                Dafny.ISequence<Dafny.Rune> _1336___mcc_h997 = _source40.dtor_name;
                                return this;
                              }
                            } else {
                              return this;
                            }
                          } else {
                            return this;
                          }
                        } else {
                          return this;
                        }
                      } else {
                        return this;
                      }
                    } else {
                      return this;
                    }
                  } else if (_source39.is_Match) {
                    RAST._IExpr _1337___mcc_h796 = _source39.dtor_matchee;
                    Dafny.ISequence<RAST._IMatchCase> _1338___mcc_h797 = _source39.dtor_cases;
                    return this;
                  } else if (_source39.is_StmtExpr) {
                    RAST._IExpr _1339___mcc_h800 = _source39.dtor_stmt;
                    RAST._IExpr _1340___mcc_h801 = _source39.dtor_rhs;
                    return this;
                  } else if (_source39.is_Block) {
                    RAST._IExpr _1341___mcc_h804 = _source39.dtor_underlying;
                    return this;
                  } else if (_source39.is_StructBuild) {
                    Dafny.ISequence<Dafny.Rune> _1342___mcc_h806 = _source39.dtor_name;
                    Dafny.ISequence<RAST._IAssignIdentifier> _1343___mcc_h807 = _source39.dtor_assignments;
                    return this;
                  } else if (_source39.is_Tuple) {
                    Dafny.ISequence<RAST._IExpr> _1344___mcc_h810 = _source39.dtor_arguments;
                    return this;
                  } else if (_source39.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> _1345___mcc_h812 = _source39.dtor_op1;
                    RAST._IExpr _1346___mcc_h813 = _source39.dtor_underlying;
                    DAST.Format._IUnaryOpFormat _1347___mcc_h814 = _source39.dtor_format;
                    return this;
                  } else if (_source39.is_BinaryOp) {
                    Dafny.ISequence<Dafny.Rune> _1348___mcc_h818 = _source39.dtor_op2;
                    RAST._IExpr _1349___mcc_h819 = _source39.dtor_left;
                    RAST._IExpr _1350___mcc_h820 = _source39.dtor_right;
                    DAST.Format._IBinaryOpFormat _1351___mcc_h821 = _source39.dtor_format2;
                    return this;
                  } else if (_source39.is_TypeAscription) {
                    RAST._IExpr _1352___mcc_h826 = _source39.dtor_left;
                    RAST._IType _1353___mcc_h827 = _source39.dtor_tpe;
                    return this;
                  } else if (_source39.is_LiteralInt) {
                    Dafny.ISequence<Dafny.Rune> _1354___mcc_h830 = _source39.dtor_value;
                    return this;
                  } else if (_source39.is_LiteralString) {
                    Dafny.ISequence<Dafny.Rune> _1355___mcc_h832 = _source39.dtor_value;
                    bool _1356___mcc_h833 = _source39.dtor_binary;
                    return this;
                  } else if (_source39.is_ConversionNum) {
                    RAST._IType _1357___mcc_h836 = _source39.dtor_tpe;
                    RAST._IExpr _1358___mcc_h837 = _source39.dtor_underlying;
                    return this;
                  } else if (_source39.is_DeclareVar) {
                    RAST._IDeclareType _1359___mcc_h840 = _source39.dtor_declareType;
                    Dafny.ISequence<Dafny.Rune> _1360___mcc_h841 = _source39.dtor_name;
                    Std.Wrappers._IOption<RAST._IType> _1361___mcc_h842 = _source39.dtor_optType;
                    Std.Wrappers._IOption<RAST._IExpr> _1362___mcc_h843 = _source39.dtor_optRhs;
                    return this;
                  } else if (_source39.is_AssignVar) {
                    Dafny.ISequence<Dafny.Rune> _1363___mcc_h848 = _source39.dtor_name;
                    RAST._IExpr _1364___mcc_h849 = _source39.dtor_rhs;
                    return this;
                  } else if (_source39.is_IfExpr) {
                    RAST._IExpr _1365___mcc_h852 = _source39.dtor_cond;
                    RAST._IExpr _1366___mcc_h853 = _source39.dtor_thn;
                    RAST._IExpr _1367___mcc_h854 = _source39.dtor_els;
                    return this;
                  } else if (_source39.is_Loop) {
                    Std.Wrappers._IOption<RAST._IExpr> _1368___mcc_h858 = _source39.dtor_optCond;
                    RAST._IExpr _1369___mcc_h859 = _source39.dtor_underlying;
                    return this;
                  } else if (_source39.is_For) {
                    Dafny.ISequence<Dafny.Rune> _1370___mcc_h862 = _source39.dtor_name;
                    RAST._IExpr _1371___mcc_h863 = _source39.dtor_range;
                    RAST._IExpr _1372___mcc_h864 = _source39.dtor_body;
                    return this;
                  } else if (_source39.is_Labelled) {
                    Dafny.ISequence<Dafny.Rune> _1373___mcc_h868 = _source39.dtor_lbl;
                    RAST._IExpr _1374___mcc_h869 = _source39.dtor_underlying;
                    return this;
                  } else if (_source39.is_Break) {
                    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1375___mcc_h872 = _source39.dtor_optLbl;
                    return this;
                  } else if (_source39.is_Continue) {
                    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1376___mcc_h874 = _source39.dtor_optLbl;
                    return this;
                  } else if (_source39.is_Return) {
                    Std.Wrappers._IOption<RAST._IExpr> _1377___mcc_h876 = _source39.dtor_optExpr;
                    return this;
                  } else if (_source39.is_Call) {
                    RAST._IExpr _1378___mcc_h878 = _source39.dtor_obj;
                    Dafny.ISequence<RAST._IType> _1379___mcc_h879 = _source39.dtor_typeParameters;
                    Dafny.ISequence<RAST._IExpr> _1380___mcc_h880 = _source39.dtor_arguments;
                    return this;
                  } else if (_source39.is_Select) {
                    RAST._IExpr _1381___mcc_h884 = _source39.dtor_obj;
                    Dafny.ISequence<Dafny.Rune> _1382___mcc_h885 = _source39.dtor_name;
                    return this;
                  } else {
                    RAST._IExpr _1383___mcc_h888 = _source39.dtor_obj;
                    Dafny.ISequence<Dafny.Rune> _1384___mcc_h889 = _source39.dtor_name;
                    return this;
                  }
                }
              }
            }
          } else if (_source35.is_Select) {
            RAST._IExpr _1385___mcc_h892 = _source35.dtor_obj;
            Dafny.ISequence<Dafny.Rune> _1386___mcc_h893 = _source35.dtor_name;
            return this;
          } else {
            RAST._IExpr _1387___mcc_h896 = _source35.dtor_obj;
            Dafny.ISequence<Dafny.Rune> _1388___mcc_h897 = _source35.dtor_name;
            return this;
          }
        } else {
          return this;
        }
      } else if (_source27.is_DeclareVar) {
        RAST._IDeclareType _1389___mcc_h348 = _source27.dtor_declareType;
        Dafny.ISequence<Dafny.Rune> _1390___mcc_h349 = _source27.dtor_name;
        Std.Wrappers._IOption<RAST._IType> _1391___mcc_h350 = _source27.dtor_optType;
        Std.Wrappers._IOption<RAST._IExpr> _1392___mcc_h351 = _source27.dtor_optRhs;
        return this;
      } else if (_source27.is_AssignVar) {
        Dafny.ISequence<Dafny.Rune> _1393___mcc_h356 = _source27.dtor_name;
        RAST._IExpr _1394___mcc_h357 = _source27.dtor_rhs;
        return this;
      } else if (_source27.is_IfExpr) {
        RAST._IExpr _1395___mcc_h360 = _source27.dtor_cond;
        RAST._IExpr _1396___mcc_h361 = _source27.dtor_thn;
        RAST._IExpr _1397___mcc_h362 = _source27.dtor_els;
        return this;
      } else if (_source27.is_Loop) {
        Std.Wrappers._IOption<RAST._IExpr> _1398___mcc_h366 = _source27.dtor_optCond;
        RAST._IExpr _1399___mcc_h367 = _source27.dtor_underlying;
        return this;
      } else if (_source27.is_For) {
        Dafny.ISequence<Dafny.Rune> _1400___mcc_h370 = _source27.dtor_name;
        RAST._IExpr _1401___mcc_h371 = _source27.dtor_range;
        RAST._IExpr _1402___mcc_h372 = _source27.dtor_body;
        return this;
      } else if (_source27.is_Labelled) {
        Dafny.ISequence<Dafny.Rune> _1403___mcc_h376 = _source27.dtor_lbl;
        RAST._IExpr _1404___mcc_h377 = _source27.dtor_underlying;
        return this;
      } else if (_source27.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1405___mcc_h380 = _source27.dtor_optLbl;
        return this;
      } else if (_source27.is_Continue) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1406___mcc_h382 = _source27.dtor_optLbl;
        return this;
      } else if (_source27.is_Return) {
        Std.Wrappers._IOption<RAST._IExpr> _1407___mcc_h384 = _source27.dtor_optExpr;
        return this;
      } else if (_source27.is_Call) {
        RAST._IExpr _1408___mcc_h386 = _source27.dtor_obj;
        Dafny.ISequence<RAST._IType> _1409___mcc_h387 = _source27.dtor_typeParameters;
        Dafny.ISequence<RAST._IExpr> _1410___mcc_h388 = _source27.dtor_arguments;
        return this;
      } else if (_source27.is_Select) {
        RAST._IExpr _1411___mcc_h392 = _source27.dtor_obj;
        Dafny.ISequence<Dafny.Rune> _1412___mcc_h393 = _source27.dtor_name;
        return this;
      } else {
        RAST._IExpr _1413___mcc_h396 = _source27.dtor_obj;
        Dafny.ISequence<Dafny.Rune> _1414___mcc_h397 = _source27.dtor_name;
        return this;
      }
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
      RAST._IExpr _source41 = this;
      if (_source41.is_RawExpr) {
        Dafny.ISequence<Dafny.Rune> _1415___mcc_h0 = _source41.dtor_content;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Identifier) {
        Dafny.ISequence<Dafny.Rune> _1416___mcc_h2 = _source41.dtor_name;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Match) {
        RAST._IExpr _1417___mcc_h4 = _source41.dtor_matchee;
        Dafny.ISequence<RAST._IMatchCase> _1418___mcc_h5 = _source41.dtor_cases;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_StmtExpr) {
        RAST._IExpr _1419___mcc_h8 = _source41.dtor_stmt;
        RAST._IExpr _1420___mcc_h9 = _source41.dtor_rhs;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Block) {
        RAST._IExpr _1421___mcc_h12 = _source41.dtor_underlying;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_StructBuild) {
        Dafny.ISequence<Dafny.Rune> _1422___mcc_h14 = _source41.dtor_name;
        Dafny.ISequence<RAST._IAssignIdentifier> _1423___mcc_h15 = _source41.dtor_assignments;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Tuple) {
        Dafny.ISequence<RAST._IExpr> _1424___mcc_h18 = _source41.dtor_arguments;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_UnaryOp) {
        Dafny.ISequence<Dafny.Rune> _1425___mcc_h20 = _source41.dtor_op1;
        RAST._IExpr _1426___mcc_h21 = _source41.dtor_underlying;
        DAST.Format._IUnaryOpFormat _1427___mcc_h22 = _source41.dtor_format;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_BinaryOp) {
        Dafny.ISequence<Dafny.Rune> _1428___mcc_h26 = _source41.dtor_op2;
        RAST._IExpr _1429___mcc_h27 = _source41.dtor_left;
        RAST._IExpr _1430___mcc_h28 = _source41.dtor_right;
        DAST.Format._IBinaryOpFormat _1431___mcc_h29 = _source41.dtor_format2;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_TypeAscription) {
        RAST._IExpr _1432___mcc_h34 = _source41.dtor_left;
        RAST._IType _1433___mcc_h35 = _source41.dtor_tpe;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_LiteralInt) {
        Dafny.ISequence<Dafny.Rune> _1434___mcc_h38 = _source41.dtor_value;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_LiteralString) {
        Dafny.ISequence<Dafny.Rune> _1435___mcc_h40 = _source41.dtor_value;
        bool _1436___mcc_h41 = _source41.dtor_binary;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_ConversionNum) {
        RAST._IType _1437___mcc_h44 = _source41.dtor_tpe;
        RAST._IExpr _1438___mcc_h45 = _source41.dtor_underlying;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_DeclareVar) {
        RAST._IDeclareType _1439___mcc_h48 = _source41.dtor_declareType;
        Dafny.ISequence<Dafny.Rune> _1440___mcc_h49 = _source41.dtor_name;
        Std.Wrappers._IOption<RAST._IType> _1441___mcc_h50 = _source41.dtor_optType;
        Std.Wrappers._IOption<RAST._IExpr> _1442___mcc_h51 = _source41.dtor_optRhs;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_AssignVar) {
        Dafny.ISequence<Dafny.Rune> _1443___mcc_h56 = _source41.dtor_name;
        RAST._IExpr _1444___mcc_h57 = _source41.dtor_rhs;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_IfExpr) {
        RAST._IExpr _1445___mcc_h60 = _source41.dtor_cond;
        RAST._IExpr _1446___mcc_h61 = _source41.dtor_thn;
        RAST._IExpr _1447___mcc_h62 = _source41.dtor_els;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Loop) {
        Std.Wrappers._IOption<RAST._IExpr> _1448___mcc_h66 = _source41.dtor_optCond;
        RAST._IExpr _1449___mcc_h67 = _source41.dtor_underlying;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_For) {
        Dafny.ISequence<Dafny.Rune> _1450___mcc_h70 = _source41.dtor_name;
        RAST._IExpr _1451___mcc_h71 = _source41.dtor_range;
        RAST._IExpr _1452___mcc_h72 = _source41.dtor_body;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Labelled) {
        Dafny.ISequence<Dafny.Rune> _1453___mcc_h76 = _source41.dtor_lbl;
        RAST._IExpr _1454___mcc_h77 = _source41.dtor_underlying;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1455___mcc_h80 = _source41.dtor_optLbl;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Continue) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1456___mcc_h82 = _source41.dtor_optLbl;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Return) {
        Std.Wrappers._IOption<RAST._IExpr> _1457___mcc_h84 = _source41.dtor_optExpr;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Call) {
        RAST._IExpr _1458___mcc_h86 = _source41.dtor_obj;
        Dafny.ISequence<RAST._IType> _1459___mcc_h87 = _source41.dtor_typeParameters;
        Dafny.ISequence<RAST._IExpr> _1460___mcc_h88 = _source41.dtor_arguments;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else if (_source41.is_Select) {
        RAST._IExpr _1461___mcc_h92 = _source41.dtor_obj;
        Dafny.ISequence<Dafny.Rune> _1462___mcc_h93 = _source41.dtor_name;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      } else {
        RAST._IExpr _1463___mcc_h96 = _source41.dtor_obj;
        Dafny.ISequence<Dafny.Rune> _1464___mcc_h97 = _source41.dtor_name;
        Dafny.ISequence<Dafny.Rune> _1465_id = _1464___mcc_h97;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1465_id);
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      var _pat_let_tv4 = ind;
      RAST._IExpr _source42 = (this).Optimize();
      if (_source42.is_RawExpr) {
        Dafny.ISequence<Dafny.Rune> _1466___mcc_h0 = _source42.dtor_content;
        RAST._IExpr _1467_r = (this).Optimize();
        return RAST.__default.AddIndent((_1467_r).dtor_content, ind);
      } else if (_source42.is_Identifier) {
        Dafny.ISequence<Dafny.Rune> _1468___mcc_h2 = _source42.dtor_name;
        Dafny.ISequence<Dafny.Rune> _1469_name = _1468___mcc_h2;
        return _1469_name;
      } else if (_source42.is_Match) {
        RAST._IExpr _1470___mcc_h4 = _source42.dtor_matchee;
        Dafny.ISequence<RAST._IMatchCase> _1471___mcc_h5 = _source42.dtor_cases;
        Dafny.ISequence<RAST._IMatchCase> _1472_cases = _1471___mcc_h5;
        RAST._IExpr _1473_matchee = _1470___mcc_h4;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match "), (_1473_matchee)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IMatchCase>(_1472_cases, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IMatchCase, Dafny.ISequence<Dafny.Rune>>>>((_1474_ind) => ((System.Func<RAST._IMatchCase, Dafny.ISequence<Dafny.Rune>>)((_1475_c) => {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _1474_ind), RAST.__default.IND), (_1475_c)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1474_ind, RAST.__default.IND)));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else if (_source42.is_StmtExpr) {
        RAST._IExpr _1476___mcc_h8 = _source42.dtor_stmt;
        RAST._IExpr _1477___mcc_h9 = _source42.dtor_rhs;
        RAST._IExpr _1478_rhs = _1477___mcc_h9;
        RAST._IExpr _1479_stmt = _1476___mcc_h8;
        if (((_1479_stmt).is_RawExpr) && (((_1479_stmt).dtor_content).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
          return (_1478_rhs)._ToString(ind);
        } else {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1479_stmt)._ToString(ind), (((_1479_stmt).NoExtraSemicolonAfter()) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), (_1478_rhs)._ToString(ind));
        }
      } else if (_source42.is_Block) {
        RAST._IExpr _1480___mcc_h12 = _source42.dtor_underlying;
        RAST._IExpr _1481_underlying = _1480___mcc_h12;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n"), ind), RAST.__default.IND), (_1481_underlying)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else if (_source42.is_StructBuild) {
        Dafny.ISequence<Dafny.Rune> _1482___mcc_h14 = _source42.dtor_name;
        Dafny.ISequence<RAST._IAssignIdentifier> _1483___mcc_h15 = _source42.dtor_assignments;
        Dafny.ISequence<RAST._IAssignIdentifier> _1484_assignments = _1483___mcc_h15;
        Dafny.ISequence<Dafny.Rune> _1485_name = _1482___mcc_h14;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1485_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IAssignIdentifier>(_1484_assignments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>>>((_1486_ind) => ((System.Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>)((_1487_assignment) => {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _1486_ind), RAST.__default.IND), (_1487_assignment)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1486_ind, RAST.__default.IND)));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_1484_assignments).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else if (_source42.is_Tuple) {
        Dafny.ISequence<RAST._IExpr> _1488___mcc_h18 = _source42.dtor_arguments;
        Dafny.ISequence<RAST._IExpr> _1489_arguments = _1488___mcc_h18;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._IExpr>(_1489_arguments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_1490_ind) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_1491_arg) => {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _1490_ind), RAST.__default.IND), (_1491_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1490_ind, RAST.__default.IND)));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_1489_arguments).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else if (_source42.is_UnaryOp) {
        Dafny.ISequence<Dafny.Rune> _1492___mcc_h20 = _source42.dtor_op1;
        RAST._IExpr _1493___mcc_h21 = _source42.dtor_underlying;
        DAST.Format._IUnaryOpFormat _1494___mcc_h22 = _source42.dtor_format;
        DAST.Format._IUnaryOpFormat _1495_format = _1494___mcc_h22;
        RAST._IExpr _1496_underlying = _1493___mcc_h21;
        Dafny.ISequence<Dafny.Rune> _1497_op = _1492___mcc_h20;
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs41 = ((((this).printingInfo).NeedParenthesesFor((_1496_underlying).printingInfo)) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))) : (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
        Dafny.ISequence<Dafny.Rune> _1498_leftP = _let_tmp_rhs41.dtor__0;
        Dafny.ISequence<Dafny.Rune> _1499_rightP = _let_tmp_rhs41.dtor__1;
        Dafny.ISequence<Dafny.Rune> _1500_leftOp = ((((_1497_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"))) && (!(_1498_leftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_1497_op, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))) : ((((_1497_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (_1497_op))));
        Dafny.ISequence<Dafny.Rune> _1501_rightOp = (((_1497_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) ? (_1497_op) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1500_leftOp, _1498_leftP), (_1496_underlying)._ToString(ind)), _1499_rightP), _1501_rightOp);
      } else if (_source42.is_BinaryOp) {
        Dafny.ISequence<Dafny.Rune> _1502___mcc_h26 = _source42.dtor_op2;
        RAST._IExpr _1503___mcc_h27 = _source42.dtor_left;
        RAST._IExpr _1504___mcc_h28 = _source42.dtor_right;
        DAST.Format._IBinaryOpFormat _1505___mcc_h29 = _source42.dtor_format2;
        DAST.Format._IBinaryOpFormat _1506_format = _1505___mcc_h29;
        RAST._IExpr _1507_right = _1504___mcc_h28;
        RAST._IExpr _1508_left = _1503___mcc_h27;
        Dafny.ISequence<Dafny.Rune> _1509_op2 = _1502___mcc_h26;
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs42 = (this).LeftParentheses(_1508_left);
        Dafny.ISequence<Dafny.Rune> _1510_leftLeftP = _let_tmp_rhs42.dtor__0;
        Dafny.ISequence<Dafny.Rune> _1511_leftRighP = _let_tmp_rhs42.dtor__1;
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs43 = (this).RightParentheses(_1507_right);
        Dafny.ISequence<Dafny.Rune> _1512_rightLeftP = _let_tmp_rhs43.dtor__0;
        Dafny.ISequence<Dafny.Rune> _1513_rightRightP = _let_tmp_rhs43.dtor__1;
        Dafny.ISequence<Dafny.Rune> _1514_opRendered = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), _1509_op2), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
        Dafny.ISequence<Dafny.Rune> _1515_indLeft = (((_1510_leftLeftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("))) ? (Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)) : (ind));
        Dafny.ISequence<Dafny.Rune> _1516_indRight = (((_1512_rightLeftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("))) ? (Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)) : (ind));
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1510_leftLeftP, (_1508_left)._ToString(_1515_indLeft)), _1511_leftRighP), _1514_opRendered), _1512_rightLeftP), (_1507_right)._ToString(_1516_indRight)), _1513_rightRightP);
      } else if (_source42.is_TypeAscription) {
        RAST._IExpr _1517___mcc_h34 = _source42.dtor_left;
        RAST._IType _1518___mcc_h35 = _source42.dtor_tpe;
        RAST._IType _1519_tpe = _1518___mcc_h35;
        RAST._IExpr _1520_left = _1517___mcc_h34;
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs44 = (this).LeftParentheses(_1520_left);
        Dafny.ISequence<Dafny.Rune> _1521_leftLeftP = _let_tmp_rhs44.dtor__0;
        Dafny.ISequence<Dafny.Rune> _1522_leftRightP = _let_tmp_rhs44.dtor__1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1521_leftLeftP, (_1520_left)._ToString(RAST.__default.IND)), _1522_leftRightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ")), (_1519_tpe)._ToString(RAST.__default.IND));
      } else if (_source42.is_LiteralInt) {
        Dafny.ISequence<Dafny.Rune> _1523___mcc_h38 = _source42.dtor_value;
        Dafny.ISequence<Dafny.Rune> _1524_number = _1523___mcc_h38;
        return _1524_number;
      } else if (_source42.is_LiteralString) {
        Dafny.ISequence<Dafny.Rune> _1525___mcc_h40 = _source42.dtor_value;
        bool _1526___mcc_h41 = _source42.dtor_binary;
        bool _1527_binary = _1526___mcc_h41;
        Dafny.ISequence<Dafny.Rune> _1528_characters = _1525___mcc_h40;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((_1527_binary) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("b")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\"")), _1528_characters), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""));
      } else if (_source42.is_ConversionNum) {
        RAST._IType _1529___mcc_h44 = _source42.dtor_tpe;
        RAST._IExpr _1530___mcc_h45 = _source42.dtor_underlying;
        RAST._IExpr _1531_expr = _1530___mcc_h45;
        RAST._IType _1532_tpe = _1529___mcc_h44;
        if (((((((((((_1532_tpe).is_U8) || ((_1532_tpe).is_U16)) || ((_1532_tpe).is_U32)) || ((_1532_tpe).is_U64)) || ((_1532_tpe).is_U128)) || ((_1532_tpe).is_I8)) || ((_1532_tpe).is_I16)) || ((_1532_tpe).is_I32)) || ((_1532_tpe).is_I64)) || ((_1532_tpe).is_I128)) {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("num::ToPrimitive::to_"), (_1532_tpe)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1531_expr)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
        } else {
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<b>Unsupported: Numeric conversion to "), (_1532_tpe)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</b>"));
        }
      } else if (_source42.is_DeclareVar) {
        RAST._IDeclareType _1533___mcc_h48 = _source42.dtor_declareType;
        Dafny.ISequence<Dafny.Rune> _1534___mcc_h49 = _source42.dtor_name;
        Std.Wrappers._IOption<RAST._IType> _1535___mcc_h50 = _source42.dtor_optType;
        Std.Wrappers._IOption<RAST._IExpr> _1536___mcc_h51 = _source42.dtor_optRhs;
        Std.Wrappers._IOption<RAST._IExpr> _1537_optExpr = _1536___mcc_h51;
        Std.Wrappers._IOption<RAST._IType> _1538_optType = _1535___mcc_h50;
        Dafny.ISequence<Dafny.Rune> _1539_name = _1534___mcc_h49;
        RAST._IDeclareType _1540_declareType = _1533___mcc_h48;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let "), ((object.Equals(_1540_declareType, RAST.DeclareType.create_MUT())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut ")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _1539_name), (((_1538_optType).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), ((_1538_optType).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), (((_1537_optExpr).is_Some) ? (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((_1537_optExpr).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)), _pat_let6_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let6_0, _1541_optExprString => (((_1541_optExprString).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("= /*issue with empty RHS*/"), ((((_1537_optExpr).dtor_value).is_RawExpr) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty Raw expr")) : (((((_1537_optExpr).dtor_value).is_LiteralString) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty string literal")) : (((((_1537_optExpr).dtor_value).is_LiteralInt) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty int literal")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Another case"))))))))) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "), _1541_optExprString)))))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
      } else if (_source42.is_AssignVar) {
        Dafny.ISequence<Dafny.Rune> _1542___mcc_h56 = _source42.dtor_name;
        RAST._IExpr _1543___mcc_h57 = _source42.dtor_rhs;
        RAST._IExpr _1544_expr = _1543___mcc_h57;
        Dafny.ISequence<Dafny.Rune> _1545_name = _1542___mcc_h56;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1545_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (_1544_expr)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
      } else if (_source42.is_IfExpr) {
        RAST._IExpr _1546___mcc_h60 = _source42.dtor_cond;
        RAST._IExpr _1547___mcc_h61 = _source42.dtor_thn;
        RAST._IExpr _1548___mcc_h62 = _source42.dtor_els;
        RAST._IExpr _1549_els = _1548___mcc_h62;
        RAST._IExpr _1550_thn = _1547___mcc_h61;
        RAST._IExpr _1551_cond = _1546___mcc_h60;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), (_1551_cond)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), ind), RAST.__default.IND), (_1550_thn)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} else {\n")), ind), RAST.__default.IND), (_1549_els)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else if (_source42.is_Loop) {
        Std.Wrappers._IOption<RAST._IExpr> _1552___mcc_h66 = _source42.dtor_optCond;
        RAST._IExpr _1553___mcc_h67 = _source42.dtor_underlying;
        RAST._IExpr _1554_underlying = _1553___mcc_h67;
        Std.Wrappers._IOption<RAST._IExpr> _1555_optCond = _1552___mcc_h66;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((System.Func<Std.Wrappers._IOption<RAST._IExpr>, Dafny.ISequence<Dafny.Rune>>)((_source43) => {
          if (_source43.is_None) {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop");
          } else {
            RAST._IExpr _1556___mcc_h100 = _source43.dtor_value;
            RAST._IExpr _1557_c = _1556___mcc_h100;
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), (_1557_c)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv4, RAST.__default.IND)));
          }
        }))(_1555_optCond), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), ind), RAST.__default.IND), (_1554_underlying)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else if (_source42.is_For) {
        Dafny.ISequence<Dafny.Rune> _1558___mcc_h70 = _source42.dtor_name;
        RAST._IExpr _1559___mcc_h71 = _source42.dtor_range;
        RAST._IExpr _1560___mcc_h72 = _source42.dtor_body;
        RAST._IExpr _1561_body = _1560___mcc_h72;
        RAST._IExpr _1562_range = _1559___mcc_h71;
        Dafny.ISequence<Dafny.Rune> _1563_name = _1558___mcc_h70;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for "), _1563_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" in ")), (_1562_range)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), ind), RAST.__default.IND), (_1561_body)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else if (_source42.is_Labelled) {
        Dafny.ISequence<Dafny.Rune> _1564___mcc_h76 = _source42.dtor_lbl;
        RAST._IExpr _1565___mcc_h77 = _source42.dtor_underlying;
        RAST._IExpr _1566_underlying = _1565___mcc_h77;
        Dafny.ISequence<Dafny.Rune> _1567_name = _1564___mcc_h76;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"), _1567_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_1566_underlying)._ToString(ind));
      } else if (_source42.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1568___mcc_h80 = _source42.dtor_optLbl;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1569_optLbl = _1568___mcc_h80;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source44 = _1569_optLbl;
        if (_source44.is_None) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;");
        } else {
          Dafny.ISequence<Dafny.Rune> _1570___mcc_h101 = _source44.dtor_value;
          Dafny.ISequence<Dafny.Rune> _1571_lbl = _1570___mcc_h101;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break '"), _1571_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      } else if (_source42.is_Continue) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1572___mcc_h82 = _source42.dtor_optLbl;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1573_optLbl = _1572___mcc_h82;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source45 = _1573_optLbl;
        if (_source45.is_None) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue;");
        } else {
          Dafny.ISequence<Dafny.Rune> _1574___mcc_h102 = _source45.dtor_value;
          Dafny.ISequence<Dafny.Rune> _1575_lbl = _1574___mcc_h102;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue '"), _1575_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      } else if (_source42.is_Return) {
        Std.Wrappers._IOption<RAST._IExpr> _1576___mcc_h84 = _source42.dtor_optExpr;
        Std.Wrappers._IOption<RAST._IExpr> _1577_optExpr = _1576___mcc_h84;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), (((_1577_optExpr).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), ((_1577_optExpr).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
      } else if (_source42.is_Call) {
        RAST._IExpr _1578___mcc_h86 = _source42.dtor_obj;
        Dafny.ISequence<RAST._IType> _1579___mcc_h87 = _source42.dtor_typeParameters;
        Dafny.ISequence<RAST._IExpr> _1580___mcc_h88 = _source42.dtor_arguments;
        Dafny.ISequence<RAST._IExpr> _1581_args = _1580___mcc_h88;
        Dafny.ISequence<RAST._IType> _1582_tpes = _1579___mcc_h87;
        RAST._IExpr _1583_expr = _1578___mcc_h86;
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs45 = (this).LeftParentheses(_1583_expr);
        Dafny.ISequence<Dafny.Rune> _1584_leftP = _let_tmp_rhs45.dtor__0;
        Dafny.ISequence<Dafny.Rune> _1585_rightP = _let_tmp_rhs45.dtor__1;
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs46 = ((System.Func<Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>>, _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>)((_source46) => {
          if (_source46.is_None) {
            return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            Dafny.ISequence<Dafny.Rune> _1586___mcc_h103 = _source46.dtor_value;
            if (object.Equals(_1586___mcc_h103, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))) {
              return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("["), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            } else if (object.Equals(_1586___mcc_h103, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))) {
              return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("["), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            } else if (object.Equals(_1586___mcc_h103, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))) {
              return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            } else if (object.Equals(_1586___mcc_h103, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))) {
              return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            } else {
              return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }
        }))((_1583_expr).RightMostIdentifier());
        Dafny.ISequence<Dafny.Rune> _1587_leftCallP = _let_tmp_rhs46.dtor__0;
        Dafny.ISequence<Dafny.Rune> _1588_rightCallP = _let_tmp_rhs46.dtor__1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1584_leftP, (_1583_expr)._ToString(ind)), _1585_rightP), (((new BigInteger((_1582_tpes).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<"), RAST.__default.SeqToString<RAST._IType>(_1582_tpes, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_1589_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_1590_tpe) => {
          return (_1590_tpe)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1589_ind, RAST.__default.IND));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))))), _1587_leftCallP), RAST.__default.SeqToString<RAST._IExpr>(_1581_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_1591_ind) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_1592_arg) => {
          return (_1592_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1591_ind, RAST.__default.IND));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), _1588_rightCallP);
      } else if (_source42.is_Select) {
        RAST._IExpr _1593___mcc_h92 = _source42.dtor_obj;
        Dafny.ISequence<Dafny.Rune> _1594___mcc_h93 = _source42.dtor_name;
        Dafny.ISequence<Dafny.Rune> _1595_name = _1594___mcc_h93;
        RAST._IExpr _1596_expression = _1593___mcc_h92;
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs47 = (this).LeftParentheses(_1596_expression);
        Dafny.ISequence<Dafny.Rune> _1597_leftP = _let_tmp_rhs47.dtor__0;
        Dafny.ISequence<Dafny.Rune> _1598_rightP = _let_tmp_rhs47.dtor__1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1597_leftP, (_1596_expression)._ToString(ind)), _1598_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1595_name);
      } else {
        RAST._IExpr _1599___mcc_h96 = _source42.dtor_obj;
        Dafny.ISequence<Dafny.Rune> _1600___mcc_h97 = _source42.dtor_name;
        Dafny.ISequence<Dafny.Rune> _1601_name = _1600___mcc_h97;
        RAST._IExpr _1602_expression = _1599___mcc_h96;
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs48 = (this).LeftParentheses(_1602_expression);
        Dafny.ISequence<Dafny.Rune> _1603_leftP = _let_tmp_rhs48.dtor__0;
        Dafny.ISequence<Dafny.Rune> _1604_rightP = _let_tmp_rhs48.dtor__1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1603_leftP, (_1602_expression)._ToString(ind)), _1604_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1601_name);
      }
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
      RAST._IExpr _source47 = this;
      if (_source47.is_RawExpr) {
        Dafny.ISequence<Dafny.Rune> _1605___mcc_h0 = _source47.dtor_content;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_Identifier) {
        Dafny.ISequence<Dafny.Rune> _1606___mcc_h2 = _source47.dtor_name;
        return RAST.PrintingInfo.create_Precedence(BigInteger.One);
      } else if (_source47.is_Match) {
        RAST._IExpr _1607___mcc_h4 = _source47.dtor_matchee;
        Dafny.ISequence<RAST._IMatchCase> _1608___mcc_h5 = _source47.dtor_cases;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_StmtExpr) {
        RAST._IExpr _1609___mcc_h8 = _source47.dtor_stmt;
        RAST._IExpr _1610___mcc_h9 = _source47.dtor_rhs;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_Block) {
        RAST._IExpr _1611___mcc_h12 = _source47.dtor_underlying;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_StructBuild) {
        Dafny.ISequence<Dafny.Rune> _1612___mcc_h14 = _source47.dtor_name;
        Dafny.ISequence<RAST._IAssignIdentifier> _1613___mcc_h15 = _source47.dtor_assignments;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_Tuple) {
        Dafny.ISequence<RAST._IExpr> _1614___mcc_h18 = _source47.dtor_arguments;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_UnaryOp) {
        Dafny.ISequence<Dafny.Rune> _1615___mcc_h20 = _source47.dtor_op1;
        RAST._IExpr _1616___mcc_h21 = _source47.dtor_underlying;
        DAST.Format._IUnaryOpFormat _1617___mcc_h22 = _source47.dtor_format;
        DAST.Format._IUnaryOpFormat _1618_format = _1617___mcc_h22;
        RAST._IExpr _1619_underlying = _1616___mcc_h21;
        Dafny.ISequence<Dafny.Rune> _1620_op = _1615___mcc_h20;
        if (object.Equals(_1620_op, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) {
          return RAST.PrintingInfo.create_SuffixPrecedence(new BigInteger(5));
        } else if (object.Equals(_1620_op, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) {
          return RAST.PrintingInfo.create_Precedence(new BigInteger(6));
        } else if (object.Equals(_1620_op, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) {
          return RAST.PrintingInfo.create_Precedence(new BigInteger(6));
        } else if (object.Equals(_1620_op, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"))) {
          return RAST.PrintingInfo.create_Precedence(new BigInteger(6));
        } else if (object.Equals(_1620_op, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
          return RAST.PrintingInfo.create_Precedence(new BigInteger(6));
        } else if (object.Equals(_1620_op, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"))) {
          return RAST.PrintingInfo.create_Precedence(new BigInteger(6));
        } else {
          return RAST.PrintingInfo.create_UnknownPrecedence();
        }
      } else if (_source47.is_BinaryOp) {
        Dafny.ISequence<Dafny.Rune> _1621___mcc_h26 = _source47.dtor_op2;
        RAST._IExpr _1622___mcc_h27 = _source47.dtor_left;
        RAST._IExpr _1623___mcc_h28 = _source47.dtor_right;
        DAST.Format._IBinaryOpFormat _1624___mcc_h29 = _source47.dtor_format2;
        DAST.Format._IBinaryOpFormat _1625_format = _1624___mcc_h29;
        RAST._IExpr _1626_right = _1623___mcc_h28;
        RAST._IExpr _1627_left = _1622___mcc_h27;
        Dafny.ISequence<Dafny.Rune> _1628_op2 = _1621___mcc_h26;
        if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(20), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(20), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(20), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(30), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(30), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(40), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(40), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(50), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(60), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(70), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(90), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||"))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(100), RAST.Associativity.create_LeftToRight());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".."))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RequiresParentheses());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RequiresParentheses());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else if (object.Equals(_1628_op2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>="))) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
        } else {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(BigInteger.Zero, RAST.Associativity.create_RequiresParentheses());
        }
      } else if (_source47.is_TypeAscription) {
        RAST._IExpr _1629___mcc_h34 = _source47.dtor_left;
        RAST._IType _1630___mcc_h35 = _source47.dtor_tpe;
        RAST._IType _1631_tpe = _1630___mcc_h35;
        RAST._IExpr _1632_left = _1629___mcc_h34;
        return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(10), RAST.Associativity.create_LeftToRight());
      } else if (_source47.is_LiteralInt) {
        Dafny.ISequence<Dafny.Rune> _1633___mcc_h38 = _source47.dtor_value;
        return RAST.PrintingInfo.create_Precedence(BigInteger.One);
      } else if (_source47.is_LiteralString) {
        Dafny.ISequence<Dafny.Rune> _1634___mcc_h40 = _source47.dtor_value;
        bool _1635___mcc_h41 = _source47.dtor_binary;
        return RAST.PrintingInfo.create_Precedence(BigInteger.One);
      } else if (_source47.is_ConversionNum) {
        RAST._IType _1636___mcc_h44 = _source47.dtor_tpe;
        RAST._IExpr _1637___mcc_h45 = _source47.dtor_underlying;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_DeclareVar) {
        RAST._IDeclareType _1638___mcc_h48 = _source47.dtor_declareType;
        Dafny.ISequence<Dafny.Rune> _1639___mcc_h49 = _source47.dtor_name;
        Std.Wrappers._IOption<RAST._IType> _1640___mcc_h50 = _source47.dtor_optType;
        Std.Wrappers._IOption<RAST._IExpr> _1641___mcc_h51 = _source47.dtor_optRhs;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_AssignVar) {
        Dafny.ISequence<Dafny.Rune> _1642___mcc_h56 = _source47.dtor_name;
        RAST._IExpr _1643___mcc_h57 = _source47.dtor_rhs;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_IfExpr) {
        RAST._IExpr _1644___mcc_h60 = _source47.dtor_cond;
        RAST._IExpr _1645___mcc_h61 = _source47.dtor_thn;
        RAST._IExpr _1646___mcc_h62 = _source47.dtor_els;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_Loop) {
        Std.Wrappers._IOption<RAST._IExpr> _1647___mcc_h66 = _source47.dtor_optCond;
        RAST._IExpr _1648___mcc_h67 = _source47.dtor_underlying;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_For) {
        Dafny.ISequence<Dafny.Rune> _1649___mcc_h70 = _source47.dtor_name;
        RAST._IExpr _1650___mcc_h71 = _source47.dtor_range;
        RAST._IExpr _1651___mcc_h72 = _source47.dtor_body;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_Labelled) {
        Dafny.ISequence<Dafny.Rune> _1652___mcc_h76 = _source47.dtor_lbl;
        RAST._IExpr _1653___mcc_h77 = _source47.dtor_underlying;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1654___mcc_h80 = _source47.dtor_optLbl;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_Continue) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1655___mcc_h82 = _source47.dtor_optLbl;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_Return) {
        Std.Wrappers._IOption<RAST._IExpr> _1656___mcc_h84 = _source47.dtor_optExpr;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      } else if (_source47.is_Call) {
        RAST._IExpr _1657___mcc_h86 = _source47.dtor_obj;
        Dafny.ISequence<RAST._IType> _1658___mcc_h87 = _source47.dtor_typeParameters;
        Dafny.ISequence<RAST._IExpr> _1659___mcc_h88 = _source47.dtor_arguments;
        return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
      } else if (_source47.is_Select) {
        RAST._IExpr _1660___mcc_h92 = _source47.dtor_obj;
        Dafny.ISequence<Dafny.Rune> _1661___mcc_h93 = _source47.dtor_name;
        Dafny.ISequence<Dafny.Rune> _1662_name = _1661___mcc_h93;
        RAST._IExpr _1663_underlying = _1660___mcc_h92;
        return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
      } else {
        RAST._IExpr _1664___mcc_h96 = _source47.dtor_obj;
        Dafny.ISequence<Dafny.Rune> _1665___mcc_h97 = _source47.dtor_name;
        Dafny.ISequence<Dafny.Rune> _1666_name = _1665___mcc_h97;
        RAST._IExpr _1667_underlying = _1664___mcc_h96;
        return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
      }
    } }
  }
  public class Expr_RawExpr : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _content;
    public Expr_RawExpr(Dafny.ISequence<Dafny.Rune> content) : base() {
      this._content = content;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_RawExpr(_content);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_RawExpr;
      return oth != null && object.Equals(this._content, oth._content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.RawExpr";
      s += "(";
      s += this._content.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_Identifier : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Expr_Identifier(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Identifier(_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Identifier;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Identifier";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_Match : Expr {
    public readonly RAST._IExpr _matchee;
    public readonly Dafny.ISequence<RAST._IMatchCase> _cases;
    public Expr_Match(RAST._IExpr matchee, Dafny.ISequence<RAST._IMatchCase> cases) : base() {
      this._matchee = matchee;
      this._cases = cases;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Match(_matchee, _cases);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Match;
      return oth != null && object.Equals(this._matchee, oth._matchee) && object.Equals(this._cases, oth._cases);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchee));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cases));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Match";
      s += "(";
      s += Dafny.Helpers.ToString(this._matchee);
      s += ", ";
      s += Dafny.Helpers.ToString(this._cases);
      s += ")";
      return s;
    }
  }
  public class Expr_StmtExpr : Expr {
    public readonly RAST._IExpr _stmt;
    public readonly RAST._IExpr _rhs;
    public Expr_StmtExpr(RAST._IExpr stmt, RAST._IExpr rhs) : base() {
      this._stmt = stmt;
      this._rhs = rhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_StmtExpr(_stmt, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_StmtExpr;
      return oth != null && object.Equals(this._stmt, oth._stmt) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._stmt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.StmtExpr";
      s += "(";
      s += Dafny.Helpers.ToString(this._stmt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rhs);
      s += ")";
      return s;
    }
  }
  public class Expr_Block : Expr {
    public readonly RAST._IExpr _underlying;
    public Expr_Block(RAST._IExpr underlying) : base() {
      this._underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Block(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Block;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Block";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_StructBuild : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._IAssignIdentifier> _assignments;
    public Expr_StructBuild(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IAssignIdentifier> assignments) : base() {
      this._name = name;
      this._assignments = assignments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_StructBuild(_name, _assignments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_StructBuild;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._assignments, oth._assignments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._assignments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.StructBuild";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._assignments);
      s += ")";
      return s;
    }
  }
  public class Expr_Tuple : Expr {
    public readonly Dafny.ISequence<RAST._IExpr> _arguments;
    public Expr_Tuple(Dafny.ISequence<RAST._IExpr> arguments) : base() {
      this._arguments = arguments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Tuple(_arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Tuple;
      return oth != null && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Tuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ")";
      return s;
    }
  }
  public class Expr_UnaryOp : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _op1;
    public readonly RAST._IExpr _underlying;
    public readonly DAST.Format._IUnaryOpFormat _format;
    public Expr_UnaryOp(Dafny.ISequence<Dafny.Rune> op1, RAST._IExpr underlying, DAST.Format._IUnaryOpFormat format) : base() {
      this._op1 = op1;
      this._underlying = underlying;
      this._format = format;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_UnaryOp(_op1, _underlying, _format);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_UnaryOp;
      return oth != null && object.Equals(this._op1, oth._op1) && object.Equals(this._underlying, oth._underlying) && object.Equals(this._format, oth._format);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._op1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._format));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.UnaryOp";
      s += "(";
      s += this._op1.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ", ";
      s += Dafny.Helpers.ToString(this._format);
      s += ")";
      return s;
    }
  }
  public class Expr_BinaryOp : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _op2;
    public readonly RAST._IExpr _left;
    public readonly RAST._IExpr _right;
    public readonly DAST.Format._IBinaryOpFormat _format2;
    public Expr_BinaryOp(Dafny.ISequence<Dafny.Rune> op2, RAST._IExpr left, RAST._IExpr right, DAST.Format._IBinaryOpFormat format2) : base() {
      this._op2 = op2;
      this._left = left;
      this._right = right;
      this._format2 = format2;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_BinaryOp(_op2, _left, _right, _format2);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_BinaryOp;
      return oth != null && object.Equals(this._op2, oth._op2) && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right) && object.Equals(this._format2, oth._format2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._op2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._format2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.BinaryOp";
      s += "(";
      s += this._op2.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ", ";
      s += Dafny.Helpers.ToString(this._format2);
      s += ")";
      return s;
    }
  }
  public class Expr_TypeAscription : Expr {
    public readonly RAST._IExpr _left;
    public readonly RAST._IType _tpe;
    public Expr_TypeAscription(RAST._IExpr left, RAST._IType tpe) : base() {
      this._left = left;
      this._tpe = tpe;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_TypeAscription(_left, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_TypeAscription;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.TypeAscription";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
  }
  public class Expr_LiteralInt : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _value;
    public Expr_LiteralInt(Dafny.ISequence<Dafny.Rune> @value) : base() {
      this._value = @value;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_LiteralInt(_value);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_LiteralInt;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.LiteralInt";
      s += "(";
      s += this._value.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_LiteralString : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _value;
    public readonly bool _binary;
    public Expr_LiteralString(Dafny.ISequence<Dafny.Rune> @value, bool binary) : base() {
      this._value = @value;
      this._binary = binary;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_LiteralString(_value, _binary);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_LiteralString;
      return oth != null && object.Equals(this._value, oth._value) && this._binary == oth._binary;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._binary));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.LiteralString";
      s += "(";
      s += this._value.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._binary);
      s += ")";
      return s;
    }
  }
  public class Expr_ConversionNum : Expr {
    public readonly RAST._IType _tpe;
    public readonly RAST._IExpr _underlying;
    public Expr_ConversionNum(RAST._IType tpe, RAST._IExpr underlying) : base() {
      this._tpe = tpe;
      this._underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_ConversionNum(_tpe, _underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_ConversionNum;
      return oth != null && object.Equals(this._tpe, oth._tpe) && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.ConversionNum";
      s += "(";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_DeclareVar : Expr {
    public readonly RAST._IDeclareType _declareType;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Std.Wrappers._IOption<RAST._IType> _optType;
    public readonly Std.Wrappers._IOption<RAST._IExpr> _optRhs;
    public Expr_DeclareVar(RAST._IDeclareType declareType, Dafny.ISequence<Dafny.Rune> name, Std.Wrappers._IOption<RAST._IType> optType, Std.Wrappers._IOption<RAST._IExpr> optRhs) : base() {
      this._declareType = declareType;
      this._name = name;
      this._optType = optType;
      this._optRhs = optRhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_DeclareVar(_declareType, _name, _optType, _optRhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_DeclareVar;
      return oth != null && object.Equals(this._declareType, oth._declareType) && object.Equals(this._name, oth._name) && object.Equals(this._optType, oth._optType) && object.Equals(this._optRhs, oth._optRhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._declareType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optRhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.DeclareVar";
      s += "(";
      s += Dafny.Helpers.ToString(this._declareType);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._optType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._optRhs);
      s += ")";
      return s;
    }
  }
  public class Expr_AssignVar : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IExpr _rhs;
    public Expr_AssignVar(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr rhs) : base() {
      this._name = name;
      this._rhs = rhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_AssignVar(_name, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_AssignVar;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.AssignVar";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rhs);
      s += ")";
      return s;
    }
  }
  public class Expr_IfExpr : Expr {
    public readonly RAST._IExpr _cond;
    public readonly RAST._IExpr _thn;
    public readonly RAST._IExpr _els;
    public Expr_IfExpr(RAST._IExpr cond, RAST._IExpr thn, RAST._IExpr els) : base() {
      this._cond = cond;
      this._thn = thn;
      this._els = els;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_IfExpr(_cond, _thn, _els);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_IfExpr;
      return oth != null && object.Equals(this._cond, oth._cond) && object.Equals(this._thn, oth._thn) && object.Equals(this._els, oth._els);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._thn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._els));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.IfExpr";
      s += "(";
      s += Dafny.Helpers.ToString(this._cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._thn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._els);
      s += ")";
      return s;
    }
  }
  public class Expr_Loop : Expr {
    public readonly Std.Wrappers._IOption<RAST._IExpr> _optCond;
    public readonly RAST._IExpr _underlying;
    public Expr_Loop(Std.Wrappers._IOption<RAST._IExpr> optCond, RAST._IExpr underlying) : base() {
      this._optCond = optCond;
      this._underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Loop(_optCond, _underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Loop;
      return oth != null && object.Equals(this._optCond, oth._optCond) && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optCond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Loop";
      s += "(";
      s += Dafny.Helpers.ToString(this._optCond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_For : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IExpr _range;
    public readonly RAST._IExpr _body;
    public Expr_For(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr range, RAST._IExpr body) : base() {
      this._name = name;
      this._range = range;
      this._body = body;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_For(_name, _range, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_For;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._range, oth._range) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._range));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.For";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._range);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class Expr_Labelled : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _lbl;
    public readonly RAST._IExpr _underlying;
    public Expr_Labelled(Dafny.ISequence<Dafny.Rune> lbl, RAST._IExpr underlying) : base() {
      this._lbl = lbl;
      this._underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Labelled(_lbl, _underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Labelled;
      return oth != null && object.Equals(this._lbl, oth._lbl) && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lbl));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Labelled";
      s += "(";
      s += this._lbl.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_Break : Expr {
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _optLbl;
    public Expr_Break(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) : base() {
      this._optLbl = optLbl;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Break(_optLbl);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Break;
      return oth != null && object.Equals(this._optLbl, oth._optLbl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optLbl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Break";
      s += "(";
      s += Dafny.Helpers.ToString(this._optLbl);
      s += ")";
      return s;
    }
  }
  public class Expr_Continue : Expr {
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _optLbl;
    public Expr_Continue(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) : base() {
      this._optLbl = optLbl;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Continue(_optLbl);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Continue;
      return oth != null && object.Equals(this._optLbl, oth._optLbl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optLbl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Continue";
      s += "(";
      s += Dafny.Helpers.ToString(this._optLbl);
      s += ")";
      return s;
    }
  }
  public class Expr_Return : Expr {
    public readonly Std.Wrappers._IOption<RAST._IExpr> _optExpr;
    public Expr_Return(Std.Wrappers._IOption<RAST._IExpr> optExpr) : base() {
      this._optExpr = optExpr;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Return(_optExpr);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Return;
      return oth != null && object.Equals(this._optExpr, oth._optExpr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optExpr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Return";
      s += "(";
      s += Dafny.Helpers.ToString(this._optExpr);
      s += ")";
      return s;
    }
  }
  public class Expr_Call : Expr {
    public readonly RAST._IExpr _obj;
    public readonly Dafny.ISequence<RAST._IType> _typeParameters;
    public readonly Dafny.ISequence<RAST._IExpr> _arguments;
    public Expr_Call(RAST._IExpr obj, Dafny.ISequence<RAST._IType> typeParameters, Dafny.ISequence<RAST._IExpr> arguments) : base() {
      this._obj = obj;
      this._typeParameters = typeParameters;
      this._arguments = arguments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Call(_obj, _typeParameters, _arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Call;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._typeParameters, oth._typeParameters) && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParameters));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParameters);
      s += ", ";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ")";
      return s;
    }
  }
  public class Expr_Select : Expr {
    public readonly RAST._IExpr _obj;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Expr_Select(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) : base() {
      this._obj = obj;
      this._name = name;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Select(_obj, _name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Select;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Select";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_MemberSelect : Expr {
    public readonly RAST._IExpr _obj;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Expr_MemberSelect(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) : base() {
      this._obj = obj;
      this._name = name;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_MemberSelect(_obj, _name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_MemberSelect;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.MemberSelect";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += this._name.ToVerbatimString(true);
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParam> _typeParams;
    public readonly Dafny.ISequence<RAST._IFormal> _formals;
    public readonly Std.Wrappers._IOption<RAST._IType> _returnType;
    public readonly Dafny.ISequence<Dafny.Rune> _where;
    public readonly Std.Wrappers._IOption<RAST._IExpr> _body;
    public Fn(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParam> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Dafny.ISequence<Dafny.Rune> @where, Std.Wrappers._IOption<RAST._IExpr> body) {
      this._name = name;
      this._typeParams = typeParams;
      this._formals = formals;
      this._returnType = returnType;
      this._where = @where;
      this._body = body;
    }
    public _IFn DowncastClone() {
      if (this is _IFn dt) { return dt; }
      return new Fn(_name, _typeParams, _formals, _returnType, _where, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Fn;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._formals, oth._formals) && object.Equals(this._returnType, oth._returnType) && object.Equals(this._where, oth._where) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._formals));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._returnType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._where));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Fn.Fn";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._formals);
      s += ", ";
      s += Dafny.Helpers.ToString(this._returnType);
      s += ", ";
      s += this._where.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
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
        return this._name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParam> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<RAST._IFormal> dtor_formals {
      get {
        return this._formals;
      }
    }
    public Std.Wrappers._IOption<RAST._IType> dtor_returnType {
      get {
        return this._returnType;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_where {
      get {
        return this._where;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_body {
      get {
        return this._body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      var _pat_let_tv5 = ind;
      var _pat_let_tv6 = ind;
      var _pat_let_tv7 = ind;
      var _pat_let_tv8 = ind;
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn "), (this).dtor_name), RAST.TypeParam.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), RAST.__default.SeqToString<RAST._IFormal>((this).dtor_formals, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>>>((_1668_ind) => ((System.Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>)((_1669_formal) => {
        return (_1669_formal)._ToString(_1668_ind);
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), ((System.Func<Std.Wrappers._IOption<RAST._IType>, Dafny.ISequence<Dafny.Rune>>)((_source48) => {
        if (_source48.is_None) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        } else {
          RAST._IType _1670___mcc_h0 = _source48.dtor_value;
          RAST._IType _1671_t = _1670___mcc_h0;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" -> "), (_1671_t)._ToString(_pat_let_tv5));
        }
      }))((this).dtor_returnType)), ((((this).dtor_where).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), (this).dtor_where)))), ((System.Func<Std.Wrappers._IOption<RAST._IExpr>, Dafny.ISequence<Dafny.Rune>>)((_source49) => {
        if (_source49.is_None) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";");
        } else {
          RAST._IExpr _1672___mcc_h2 = _source49.dtor_value;
          RAST._IExpr _1673_body = _1672___mcc_h2;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"), _pat_let_tv6), RAST.__default.IND), (_1673_body)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv7, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv8), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }))((this).dtor_body));
    }
  }
} // end of namespace RAST