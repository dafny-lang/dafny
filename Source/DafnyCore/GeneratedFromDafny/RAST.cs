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
    public static RAST._IType ObjectType(RAST._IType underlying) {
      return ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IType Rc(RAST._IType underlying) {
      return RAST.Type.create_TypeApp(RAST.__default.RcType, Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IType RefCell(RAST._IType underlying) {
      return RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cell"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("RefCell")), Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IType Vec(RAST._IType underlying) {
      return RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Vec")), Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IExpr NewVec(Dafny.ISequence<RAST._IExpr> elements) {
      return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec!"))).Apply(elements);
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
    public static RAST._IType Box(RAST._IType content) {
      return RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Box")), Dafny.Sequence<RAST._IType>.FromElements(content));
    }
    public static RAST._IExpr BoxNew(RAST._IExpr content) {
      return ((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Box"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(content));
    }
    public static RAST._IType SystemTupleType(Dafny.ISequence<RAST._IType> elements) {
      return (((RAST.__default.super__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Tuple"), Std.Strings.__default.OfNat(new BigInteger((elements).Count))))).Apply(elements);
    }
    public static RAST._IExpr SystemTuple(Dafny.ISequence<RAST._IExpr> elements) {
      Dafny.ISequence<Dafny.Rune> _800_size = Std.Strings.__default.OfNat(new BigInteger((elements).Count));
      return RAST.Expr.create_StructBuild((((RAST.__default.super).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Tuple"), _800_size))).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), _800_size)), ((System.Func<Dafny.ISequence<RAST._IAssignIdentifier>>) (() => {
  BigInteger dim10 = new BigInteger((elements).Count);
  var arr10 = new RAST._IAssignIdentifier[Dafny.Helpers.ToIntChecked(dim10, "array size exceeds memory limit")];
  for (int i10 = 0; i10 < dim10; i10++) {
    var _801_i = (BigInteger) i10;
    arr10[(int)(_801_i)] = RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), Std.Strings.__default.OfNat(_801_i)), (elements).Select(_801_i));
  }
  return Dafny.Sequence<RAST._IAssignIdentifier>.FromArray(arr10);
}))());
    }
    public static RAST._IType MaybeUninitType(RAST._IType underlying) {
      return (RAST.__default.MaybeUninitPath).Apply(Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static bool IsMaybeUninitType(RAST._IType tpe) {
      return (((tpe).is_TypeApp) && (object.Equals((tpe).dtor_baseName, RAST.__default.MaybeUninitPath))) && ((new BigInteger(((tpe).dtor_arguments).Count)) == (BigInteger.One));
    }
    public static RAST._IType MaybeUninitTypeUnderlying(RAST._IType tpe) {
      return ((tpe).dtor_arguments).Select(BigInteger.Zero);
    }
    public static RAST._IExpr MaybeUninitNew(RAST._IExpr underlying) {
      return ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mem"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybeUninit"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(underlying));
    }
    public static RAST._IType MaybePlaceboType(RAST._IType underlying) {
      return ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).Apply1(underlying);
    }
    public static Dafny.ISequence<Dafny.Rune> AddIndent(Dafny.ISequence<Dafny.Rune> raw, Dafny.ISequence<Dafny.Rune> ind)
    {
      Dafny.ISequence<Dafny.Rune> _802___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((raw).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_802___accumulator, raw);
      } else if ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[({")).Contains((raw).Select(BigInteger.Zero))) {
        _802___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_802___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in103 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in104 = Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND);
        raw = _in103;
        ind = _in104;
        goto TAIL_CALL_START;
      } else if (((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("})]")).Contains((raw).Select(BigInteger.Zero))) && ((new BigInteger((ind).Count)) > (new BigInteger(2)))) {
        _802___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_802___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in105 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in106 = (ind).Take((new BigInteger((ind).Count)) - (new BigInteger(2)));
        raw = _in105;
        ind = _in106;
        goto TAIL_CALL_START;
      } else if (((raw).Select(BigInteger.Zero)) == (new Dafny.Rune('\n'))) {
        _802___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_802___accumulator, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)), ind));
        Dafny.ISequence<Dafny.Rune> _in107 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in108 = ind;
        raw = _in107;
        ind = _in108;
        goto TAIL_CALL_START;
      } else {
        _802___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_802___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
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
    public static RAST._IExpr AssignVar(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr rhs)
    {
      return RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_LocalVar(name)), rhs);
    }
    public static RAST._IExpr AssignMember(RAST._IExpr @on, Dafny.ISequence<Dafny.Rune> field, RAST._IExpr rhs)
    {
      return RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_SelectMember(@on, field)), rhs);
    }
    public static RAST._IExpr MaybePlacebo(RAST._IExpr underlying) {
      return (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(underlying);
    }
    public static RAST._IExpr RcNew(RAST._IExpr underlying) {
      return RAST.Expr.create_Call(RAST.__default.std__rc__Rc__new, Dafny.Sequence<RAST._IExpr>.FromElements(underlying));
    }
    public static RAST._IExpr IntoUsize(RAST._IExpr underlying) {
      return (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyUsize"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into_usize"))).Apply1(underlying);
    }
    public static RAST._IType SelfBorrowed { get {
      return RAST.Type.create_Borrowed(RAST.Type.create_SelfOwned());
    } }
    public static RAST._IType SelfBorrowedMut { get {
      return RAST.Type.create_BorrowedMut(RAST.Type.create_SelfOwned());
    } }
    public static RAST._IType SelfPointer { get {
      return RAST.Type.create_Pointer(RAST.Type.create_SelfOwned());
    } }
    public static RAST._IType SelfPointerMut { get {
      return RAST.Type.create_PointerMut(RAST.Type.create_SelfOwned());
    } }
    public static RAST._IType global__type { get {
      return RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
    } }
    public static RAST._IType std__type { get {
      return (RAST.__default.global__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"));
    } }
    public static RAST._IType RcType { get {
      return ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Rc"));
    } }
    public static RAST._IType dafny__runtime__type { get {
      return (RAST.__default.global__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime"));
    } }
    public static RAST._IType super__type { get {
      return RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"));
    } }
    public static RAST._IType cell__type { get {
      return (RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cell"));
    } }
    public static RAST._IType refcell__type { get {
      return (RAST.__default.cell__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("RefCell"));
    } }
    public static RAST._IType CloneTrait { get {
      return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Clone"));
    } }
    public static RAST._IType DefaultTrait { get {
      return ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"));
    } }
    public static RAST._IType StaticTrait { get {
      return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'static"));
    } }
    public static RAST._IType DafnyType { get {
      return (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyType"));
    } }
    public static RAST._IType DafnyPrint { get {
      return (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"));
    } }
    public static RAST._IType DafnyTypeEq { get {
      return (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyTypeEq"));
    } }
    public static RAST._IType Eq { get {
      return RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Eq"));
    } }
    public static RAST._IType Hash { get {
      return ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"));
    } }
    public static RAST._IType DafnyInt { get {
      return (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
    } }
    public static RAST._IExpr super { get {
      return RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"));
    } }
    public static RAST._IType MaybeUninitPath { get {
      return ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mem"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybeUninit"));
    } }
    public static RAST._IExpr @global { get {
      return RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
    } }
    public static RAST._IExpr std { get {
      return (RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"));
    } }
    public static Dafny.ISequence<Dafny.Rune> IND { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  ");
    } }
    public static RAST._IExpr self { get {
      return RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"));
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
    public static RAST._IExpr std__rc { get {
      return (RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc"));
    } }
    public static RAST._IExpr std__rc__Rc { get {
      return (RAST.__default.std__rc).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Rc"));
    } }
    public static RAST._IExpr std__rc__Rc__new { get {
      return (RAST.__default.std__rc__Rc).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"));
    } }
    public static RAST._IExpr std__Default__default { get {
      return ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
    } }
    public static BigInteger MAX__TUPLE__SIZE { get {
      return new BigInteger(12);
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
      var _pat_let_tv37 = ind;
      var _pat_let_tv38 = ind;
      var _pat_let_tv39 = ind;
      var _pat_let_tv40 = ind;
      RAST._IMod _source29 = this;
      bool unmatched29 = true;
      if (unmatched29) {
        if (_source29.is_ExternMod) {
          Dafny.ISequence<Dafny.Rune> _803_name = _source29.dtor_name;
          unmatched29 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub mod "), _803_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      if (unmatched29) {
        Dafny.ISequence<Dafny.Rune> _804_name = _source29.dtor_name;
        Dafny.ISequence<RAST._IModDecl> _805_body = _source29.dtor_body;
        unmatched29 = false;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub mod "), _804_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv37), RAST.__default.IND), RAST.__default.SeqToString<RAST._IModDecl>(_805_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IModDecl, Dafny.ISequence<Dafny.Rune>>>>((_806_ind) => ((System.Func<RAST._IModDecl, Dafny.ISequence<Dafny.Rune>>)((_807_modDecl) => {
          return (_807_modDecl)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_806_ind, RAST.__default.IND));
        })))(_pat_let_tv38), Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n\n"), _pat_let_tv39), RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv40), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      }
      throw new System.Exception("unexpected control point");
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
    bool is_TypeDecl { get; }
    bool is_ConstDecl { get; }
    bool is_EnumDecl { get; }
    bool is_ImplDecl { get; }
    bool is_TraitDecl { get; }
    bool is_TopFnDecl { get; }
    bool is_UseDecl { get; }
    Dafny.ISequence<Dafny.Rune> dtor_body { get; }
    RAST._IMod dtor_mod { get; }
    RAST._IStruct dtor_struct { get; }
    RAST._ITypeSynonym dtor_tpe { get; }
    RAST._IConstant dtor_c { get; }
    RAST._IEnum dtor_enum { get; }
    RAST._IImpl dtor_impl { get; }
    RAST._ITrait dtor_tr { get; }
    RAST._ITopFnDecl dtor_fn { get; }
    RAST._IUse dtor_use { get; }
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
    public static _IModDecl create_TypeDecl(RAST._ITypeSynonym tpe) {
      return new ModDecl_TypeDecl(tpe);
    }
    public static _IModDecl create_ConstDecl(RAST._IConstant c) {
      return new ModDecl_ConstDecl(c);
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
    public static _IModDecl create_TopFnDecl(RAST._ITopFnDecl fn) {
      return new ModDecl_TopFnDecl(fn);
    }
    public static _IModDecl create_UseDecl(RAST._IUse use) {
      return new ModDecl_UseDecl(use);
    }
    public bool is_RawDecl { get { return this is ModDecl_RawDecl; } }
    public bool is_ModDecl { get { return this is ModDecl_ModDecl; } }
    public bool is_StructDecl { get { return this is ModDecl_StructDecl; } }
    public bool is_TypeDecl { get { return this is ModDecl_TypeDecl; } }
    public bool is_ConstDecl { get { return this is ModDecl_ConstDecl; } }
    public bool is_EnumDecl { get { return this is ModDecl_EnumDecl; } }
    public bool is_ImplDecl { get { return this is ModDecl_ImplDecl; } }
    public bool is_TraitDecl { get { return this is ModDecl_TraitDecl; } }
    public bool is_TopFnDecl { get { return this is ModDecl_TopFnDecl; } }
    public bool is_UseDecl { get { return this is ModDecl_UseDecl; } }
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
    public RAST._ITypeSynonym dtor_tpe {
      get {
        var d = this;
        return ((ModDecl_TypeDecl)d)._tpe;
      }
    }
    public RAST._IConstant dtor_c {
      get {
        var d = this;
        return ((ModDecl_ConstDecl)d)._c;
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
    public RAST._ITopFnDecl dtor_fn {
      get {
        var d = this;
        return ((ModDecl_TopFnDecl)d)._fn;
      }
    }
    public RAST._IUse dtor_use {
      get {
        var d = this;
        return ((ModDecl_UseDecl)d)._use;
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
      } else if ((this).is_TypeDecl) {
        return ((this).dtor_tpe)._ToString(ind);
      } else if ((this).is_ConstDecl) {
        return ((this).dtor_c)._ToString(ind);
      } else if ((this).is_TraitDecl) {
        return ((this).dtor_tr)._ToString(ind);
      } else if ((this).is_TopFnDecl) {
        return ((this).dtor_fn)._ToString(ind);
      } else if ((this).is_UseDecl) {
        return ((this).dtor_use)._ToString(ind);
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
  public class ModDecl_TypeDecl : ModDecl {
    public readonly RAST._ITypeSynonym _tpe;
    public ModDecl_TypeDecl(RAST._ITypeSynonym tpe) : base() {
      this._tpe = tpe;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_TypeDecl(_tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_TypeDecl;
      return oth != null && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.TypeDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
  }
  public class ModDecl_ConstDecl : ModDecl {
    public readonly RAST._IConstant _c;
    public ModDecl_ConstDecl(RAST._IConstant c) : base() {
      this._c = c;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_ConstDecl(_c);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_ConstDecl;
      return oth != null && object.Equals(this._c, oth._c);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._c));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.ConstDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._c);
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
      hash = ((hash << 5) + hash) + 5;
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
      hash = ((hash << 5) + hash) + 6;
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
      hash = ((hash << 5) + hash) + 7;
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
  public class ModDecl_TopFnDecl : ModDecl {
    public readonly RAST._ITopFnDecl _fn;
    public ModDecl_TopFnDecl(RAST._ITopFnDecl fn) : base() {
      this._fn = fn;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_TopFnDecl(_fn);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_TopFnDecl;
      return oth != null && object.Equals(this._fn, oth._fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.TopFnDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._fn);
      s += ")";
      return s;
    }
  }
  public class ModDecl_UseDecl : ModDecl {
    public readonly RAST._IUse _use;
    public ModDecl_UseDecl(RAST._IUse use) : base() {
      this._use = use;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_UseDecl(_use);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_UseDecl;
      return oth != null && object.Equals(this._use, oth._use);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._use));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.UseDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._use);
      s += ")";
      return s;
    }
  }

  public interface _IUse {
    bool is_Use { get; }
    RAST._IVisibility dtor_visibility { get; }
    RAST._IExpr dtor_path { get; }
    _IUse DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Use : _IUse {
    public readonly RAST._IVisibility _visibility;
    public readonly RAST._IExpr _path;
    public Use(RAST._IVisibility visibility, RAST._IExpr path) {
      this._visibility = visibility;
      this._path = path;
    }
    public _IUse DowncastClone() {
      if (this is _IUse dt) { return dt; }
      return new Use(_visibility, _path);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Use;
      return oth != null && object.Equals(this._visibility, oth._visibility) && object.Equals(this._path, oth._path);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visibility));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Use.Use";
      s += "(";
      s += Dafny.Helpers.ToString(this._visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._path);
      s += ")";
      return s;
    }
    private static readonly RAST._IUse theDefault = create(RAST.Visibility.Default(), RAST.Expr.Default());
    public static RAST._IUse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IUse> _TYPE = new Dafny.TypeDescriptor<RAST._IUse>(RAST.Use.Default());
    public static Dafny.TypeDescriptor<RAST._IUse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUse create(RAST._IVisibility visibility, RAST._IExpr path) {
      return new Use(visibility, path);
    }
    public static _IUse create_Use(RAST._IVisibility visibility, RAST._IExpr path) {
      return create(visibility, path);
    }
    public bool is_Use { get { return true; } }
    public RAST._IVisibility dtor_visibility {
      get {
        return this._visibility;
      }
    }
    public RAST._IExpr dtor_path {
      get {
        return this._path;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_visibility)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use ")), ((this).dtor_path)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
    }
  }

  public interface _ITopFnDecl {
    bool is_TopFn { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_attributes { get; }
    RAST._IVisibility dtor_visibility { get; }
    RAST._IFn dtor_fn { get; }
    _ITopFnDecl DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class TopFnDecl : _ITopFnDecl {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _attributes;
    public readonly RAST._IVisibility _visibility;
    public readonly RAST._IFn _fn;
    public TopFnDecl(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, RAST._IVisibility visibility, RAST._IFn fn) {
      this._attributes = attributes;
      this._visibility = visibility;
      this._fn = fn;
    }
    public _ITopFnDecl DowncastClone() {
      if (this is _ITopFnDecl dt) { return dt; }
      return new TopFnDecl(_attributes, _visibility, _fn);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.TopFnDecl;
      return oth != null && object.Equals(this._attributes, oth._attributes) && object.Equals(this._visibility, oth._visibility) && object.Equals(this._fn, oth._fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visibility));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.TopFnDecl.TopFn";
      s += "(";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fn);
      s += ")";
      return s;
    }
    private static readonly RAST._ITopFnDecl theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, RAST.Visibility.Default(), RAST.Fn.Default());
    public static RAST._ITopFnDecl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITopFnDecl> _TYPE = new Dafny.TypeDescriptor<RAST._ITopFnDecl>(RAST.TopFnDecl.Default());
    public static Dafny.TypeDescriptor<RAST._ITopFnDecl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITopFnDecl create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, RAST._IVisibility visibility, RAST._IFn fn) {
      return new TopFnDecl(attributes, visibility, fn);
    }
    public static _ITopFnDecl create_TopFn(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, RAST._IVisibility visibility, RAST._IFn fn) {
      return create(attributes, visibility, fn);
    }
    public bool is_TopFn { get { return true; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public RAST._IVisibility dtor_visibility {
      get {
        return this._visibility;
      }
    }
    public RAST._IFn dtor_fn {
      get {
        return this._fn;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind), ((this).dtor_visibility)._ToString()), ((this).dtor_fn)._ToString(ind));
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
      return RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(attributes, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>>((_808_ind) => ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_809_attribute) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_809_attribute), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _808_ind);
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
    }
  }

  public interface _IStruct {
    bool is_Struct { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    RAST._IFields dtor_fields { get; }
    _IStruct DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Struct : _IStruct {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IFields _fields;
    public Struct(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IFields fields) {
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
    private static readonly RAST._IStruct theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParamDecl>.Empty, RAST.Fields.Default());
    public static RAST._IStruct Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IStruct> _TYPE = new Dafny.TypeDescriptor<RAST._IStruct>(RAST.Struct.Default());
    public static Dafny.TypeDescriptor<RAST._IStruct> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStruct create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IFields fields) {
      return new Struct(attributes, name, typeParams, fields);
    }
    public static _IStruct create_Struct(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IFields fields) {
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
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public RAST._IFields dtor_fields {
      get {
        return this._fields;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub struct ")), (this).dtor_name), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), ((this).dtor_fields)._ToString(ind, ((this).dtor_fields).is_NamedFields)), ((((this).dtor_fields).is_NamelessFields) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
    }
  }

  public interface _ITypeSynonym {
    bool is_TypeSynonym { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    RAST._IType dtor_tpe { get; }
    _ITypeSynonym DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class TypeSynonym : _ITypeSynonym {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IType _tpe;
    public TypeSynonym(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe) {
      this._attributes = attributes;
      this._name = name;
      this._typeParams = typeParams;
      this._tpe = tpe;
    }
    public _ITypeSynonym DowncastClone() {
      if (this is _ITypeSynonym dt) { return dt; }
      return new TypeSynonym(_attributes, _name, _typeParams, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.TypeSynonym;
      return oth != null && object.Equals(this._attributes, oth._attributes) && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.TypeSynonym.TypeSynonym";
      s += "(";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
    private static readonly RAST._ITypeSynonym theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParamDecl>.Empty, RAST.Type.Default());
    public static RAST._ITypeSynonym Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITypeSynonym> _TYPE = new Dafny.TypeDescriptor<RAST._ITypeSynonym>(RAST.TypeSynonym.Default());
    public static Dafny.TypeDescriptor<RAST._ITypeSynonym> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITypeSynonym create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe) {
      return new TypeSynonym(attributes, name, typeParams, tpe);
    }
    public static _ITypeSynonym create_TypeSynonym(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe) {
      return create(attributes, name, typeParams, tpe);
    }
    public bool is_TypeSynonym { get { return true; } }
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
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub type ")), (this).dtor_name), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), ((this).dtor_tpe)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
    }
  }

  public interface _IConstant {
    bool is_Constant { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IType dtor_tpe { get; }
    RAST._IExpr dtor_value { get; }
    _IConstant DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Constant : _IConstant {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IType _tpe;
    public readonly RAST._IExpr _value;
    public Constant(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe, RAST._IExpr @value) {
      this._attributes = attributes;
      this._name = name;
      this._tpe = tpe;
      this._value = @value;
    }
    public _IConstant DowncastClone() {
      if (this is _IConstant dt) { return dt; }
      return new Constant(_attributes, _name, _tpe, _value);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Constant;
      return oth != null && object.Equals(this._attributes, oth._attributes) && object.Equals(this._name, oth._name) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Constant.Constant";
      s += "(";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
    private static readonly RAST._IConstant theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, RAST.Type.Default(), RAST.Expr.Default());
    public static RAST._IConstant Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IConstant> _TYPE = new Dafny.TypeDescriptor<RAST._IConstant>(RAST.Constant.Default());
    public static Dafny.TypeDescriptor<RAST._IConstant> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConstant create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe, RAST._IExpr @value) {
      return new Constant(attributes, name, tpe, @value);
    }
    public static _IConstant create_Constant(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe, RAST._IExpr @value) {
      return create(attributes, name, tpe, @value);
    }
    public bool is_Constant { get { return true; } }
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
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
      }
    }
    public RAST._IExpr dtor_value {
      get {
        return this._value;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub const ")), (this).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((this).dtor_tpe)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=")), ((this).dtor_value)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
    }
  }

  public interface _INamelessField {
    bool is_NamelessField { get; }
    RAST._IVisibility dtor_visibility { get; }
    RAST._IType dtor_tpe { get; }
    _INamelessField DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class NamelessField : _INamelessField {
    public readonly RAST._IVisibility _visibility;
    public readonly RAST._IType _tpe;
    public NamelessField(RAST._IVisibility visibility, RAST._IType tpe) {
      this._visibility = visibility;
      this._tpe = tpe;
    }
    public _INamelessField DowncastClone() {
      if (this is _INamelessField dt) { return dt; }
      return new NamelessField(_visibility, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.NamelessField;
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
      string s = "RAST.NamelessField.NamelessField";
      s += "(";
      s += Dafny.Helpers.ToString(this._visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
    private static readonly RAST._INamelessField theDefault = create(RAST.Visibility.Default(), RAST.Type.Default());
    public static RAST._INamelessField Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._INamelessField> _TYPE = new Dafny.TypeDescriptor<RAST._INamelessField>(RAST.NamelessField.Default());
    public static Dafny.TypeDescriptor<RAST._INamelessField> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INamelessField create(RAST._IVisibility visibility, RAST._IType tpe) {
      return new NamelessField(visibility, tpe);
    }
    public static _INamelessField create_NamelessField(RAST._IVisibility visibility, RAST._IType tpe) {
      return create(visibility, tpe);
    }
    public bool is_NamelessField { get { return true; } }
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
      return Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_visibility)._ToString(), ((this).dtor_tpe)._ToString(ind));
    }
  }

  public interface _IField {
    bool is_Field { get; }
    RAST._IVisibility dtor_visibility { get; }
    RAST._IFormal dtor_formal { get; }
    _IField DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
    RAST._INamelessField ToNamelessField();
  }
  public class Field : _IField {
    public readonly RAST._IVisibility _visibility;
    public readonly RAST._IFormal _formal;
    public Field(RAST._IVisibility visibility, RAST._IFormal formal) {
      this._visibility = visibility;
      this._formal = formal;
    }
    public _IField DowncastClone() {
      if (this is _IField dt) { return dt; }
      return new Field(_visibility, _formal);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Field;
      return oth != null && object.Equals(this._visibility, oth._visibility) && object.Equals(this._formal, oth._formal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visibility));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._formal));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Field.Field";
      s += "(";
      s += Dafny.Helpers.ToString(this._visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._formal);
      s += ")";
      return s;
    }
    private static readonly RAST._IField theDefault = create(RAST.Visibility.Default(), RAST.Formal.Default());
    public static RAST._IField Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IField> _TYPE = new Dafny.TypeDescriptor<RAST._IField>(RAST.Field.Default());
    public static Dafny.TypeDescriptor<RAST._IField> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IField create(RAST._IVisibility visibility, RAST._IFormal formal) {
      return new Field(visibility, formal);
    }
    public static _IField create_Field(RAST._IVisibility visibility, RAST._IFormal formal) {
      return create(visibility, formal);
    }
    public bool is_Field { get { return true; } }
    public RAST._IVisibility dtor_visibility {
      get {
        return this._visibility;
      }
    }
    public RAST._IFormal dtor_formal {
      get {
        return this._formal;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_visibility)._ToString(), ((this).dtor_formal)._ToString(ind));
    }
    public RAST._INamelessField ToNamelessField() {
      return RAST.NamelessField.create((this).dtor_visibility, ((this).dtor_formal).dtor_tpe);
    }
  }

  public interface _IFields {
    bool is_NamedFields { get; }
    bool is_NamelessFields { get; }
    Dafny.ISequence<RAST._IField> dtor_fields { get; }
    Dafny.ISequence<RAST._INamelessField> dtor_types { get; }
    _IFields DowncastClone();
    RAST._IFields ToNamelessFields();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine);
  }
  public abstract class Fields : _IFields {
    public Fields() {
    }
    private static readonly RAST._IFields theDefault = create_NamedFields(Dafny.Sequence<RAST._IField>.Empty);
    public static RAST._IFields Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IFields> _TYPE = new Dafny.TypeDescriptor<RAST._IFields>(RAST.Fields.Default());
    public static Dafny.TypeDescriptor<RAST._IFields> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFields create_NamedFields(Dafny.ISequence<RAST._IField> fields) {
      return new Fields_NamedFields(fields);
    }
    public static _IFields create_NamelessFields(Dafny.ISequence<RAST._INamelessField> types) {
      return new Fields_NamelessFields(types);
    }
    public bool is_NamedFields { get { return this is Fields_NamedFields; } }
    public bool is_NamelessFields { get { return this is Fields_NamelessFields; } }
    public Dafny.ISequence<RAST._IField> dtor_fields {
      get {
        var d = this;
        return ((Fields_NamedFields)d)._fields;
      }
    }
    public Dafny.ISequence<RAST._INamelessField> dtor_types {
      get {
        var d = this;
        return ((Fields_NamelessFields)d)._types;
      }
    }
    public abstract _IFields DowncastClone();
    public RAST._IFields ToNamelessFields() {
      return RAST.Fields.create_NamelessFields(((System.Func<Dafny.ISequence<RAST._INamelessField>>) (() => {
  BigInteger dim11 = new BigInteger(((this).dtor_fields).Count);
  var arr11 = new RAST._INamelessField[Dafny.Helpers.ToIntChecked(dim11, "array size exceeds memory limit")];
  for (int i11 = 0; i11 < dim11; i11++) {
    var _810_i = (BigInteger) i11;
    arr11[(int)(_810_i)] = (((this).dtor_fields).Select(_810_i)).ToNamelessField();
  }
  return Dafny.Sequence<RAST._INamelessField>.FromArray(arr11);
}))());
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine)
    {
      if ((this).is_NamedFields) {
        Dafny.ISequence<Dafny.Rune> _811_separator = ((newLine) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")));
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs40 = (((newLine) && ((new BigInteger(((this).dtor_fields).Count)).Sign == 1)) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind))) : ((((new BigInteger(((this).dtor_fields).Count)).Sign == 1) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))) : (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
        Dafny.ISequence<Dafny.Rune> _812_beginSpace = _let_tmp_rhs40.dtor__0;
        Dafny.ISequence<Dafny.Rune> _813_endSpace = _let_tmp_rhs40.dtor__1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"), _812_beginSpace), RAST.__default.SeqToString<RAST._IField>((this).dtor_fields, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IField, Dafny.ISequence<Dafny.Rune>>>>((_814_ind) => ((System.Func<RAST._IField, Dafny.ISequence<Dafny.Rune>>)((_815_field) => {
          return (_815_field)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_814_ind, RAST.__default.IND));
        })))(ind), _811_separator)), _813_endSpace), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else {
        Dafny.ISequence<Dafny.Rune> _816_separator = ((newLine) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")));
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._INamelessField>((this).dtor_types, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._INamelessField, Dafny.ISequence<Dafny.Rune>>>>((_817_ind) => ((System.Func<RAST._INamelessField, Dafny.ISequence<Dafny.Rune>>)((_818_t) => {
          return (_818_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_817_ind, RAST.__default.IND));
        })))(ind), _816_separator)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
    }
  }
  public class Fields_NamedFields : Fields {
    public readonly Dafny.ISequence<RAST._IField> _fields;
    public Fields_NamedFields(Dafny.ISequence<RAST._IField> fields) : base() {
      this._fields = fields;
    }
    public override _IFields DowncastClone() {
      if (this is _IFields dt) { return dt; }
      return new Fields_NamedFields(_fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Fields_NamedFields;
      return oth != null && object.Equals(this._fields, oth._fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Fields.NamedFields";
      s += "(";
      s += Dafny.Helpers.ToString(this._fields);
      s += ")";
      return s;
    }
  }
  public class Fields_NamelessFields : Fields {
    public readonly Dafny.ISequence<RAST._INamelessField> _types;
    public Fields_NamelessFields(Dafny.ISequence<RAST._INamelessField> types) : base() {
      this._types = types;
    }
    public override _IFields DowncastClone() {
      if (this is _IFields dt) { return dt; }
      return new Fields_NamelessFields(_types);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Fields_NamelessFields;
      return oth != null && object.Equals(this._types, oth._types);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._types));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Fields.NamelessFields";
      s += "(";
      s += Dafny.Helpers.ToString(this._types);
      s += ")";
      return s;
    }
  }

  public interface _IEnumCase {
    bool is_EnumCase { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IFields dtor_fields { get; }
    _IEnumCase DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine);
  }
  public class EnumCase : _IEnumCase {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IFields _fields;
    public EnumCase(Dafny.ISequence<Dafny.Rune> name, RAST._IFields fields) {
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
    private static readonly RAST._IEnumCase theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, RAST.Fields.Default());
    public static RAST._IEnumCase Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IEnumCase> _TYPE = new Dafny.TypeDescriptor<RAST._IEnumCase>(RAST.EnumCase.Default());
    public static Dafny.TypeDescriptor<RAST._IEnumCase> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnumCase create(Dafny.ISequence<Dafny.Rune> name, RAST._IFields fields) {
      return new EnumCase(name, fields);
    }
    public static _IEnumCase create_EnumCase(Dafny.ISequence<Dafny.Rune> name, RAST._IFields fields) {
      return create(name, fields);
    }
    public bool is_EnumCase { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public RAST._IFields dtor_fields {
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
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    Dafny.ISequence<RAST._IEnumCase> dtor_variants { get; }
    _IEnum DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Enum : _IEnum {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly Dafny.ISequence<RAST._IEnumCase> _variants;
    public Enum(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
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
    private static readonly RAST._IEnum theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParamDecl>.Empty, Dafny.Sequence<RAST._IEnumCase>.Empty);
    public static RAST._IEnum Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IEnum> _TYPE = new Dafny.TypeDescriptor<RAST._IEnum>(RAST.Enum.Default());
    public static Dafny.TypeDescriptor<RAST._IEnum> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnum create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
      return new Enum(attributes, name, typeParams, variants);
    }
    public static _IEnum create_Enum(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
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
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
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
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub enum ")), (this).dtor_name), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IEnumCase>((this).dtor_variants, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IEnumCase, Dafny.ISequence<Dafny.Rune>>>>((_819_ind) => ((System.Func<RAST._IEnumCase, Dafny.ISequence<Dafny.Rune>>)((_820_variant) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _819_ind), RAST.__default.IND), (_820_variant)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_819_ind, RAST.__default.IND), true));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }

  public interface _ITypeParamDecl {
    bool is_TypeParamDecl { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
    Dafny.ISequence<RAST._IType> dtor_constraints { get; }
    _ITypeParamDecl DowncastClone();
    RAST._ITypeParamDecl AddConstraints(Dafny.ISequence<RAST._IType> constraints);
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class TypeParamDecl : _ITypeParamDecl {
    public readonly Dafny.ISequence<Dafny.Rune> _content;
    public readonly Dafny.ISequence<RAST._IType> _constraints;
    public TypeParamDecl(Dafny.ISequence<Dafny.Rune> content, Dafny.ISequence<RAST._IType> constraints) {
      this._content = content;
      this._constraints = constraints;
    }
    public _ITypeParamDecl DowncastClone() {
      if (this is _ITypeParamDecl dt) { return dt; }
      return new TypeParamDecl(_content, _constraints);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.TypeParamDecl;
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
      string s = "RAST.TypeParamDecl.TypeParamDecl";
      s += "(";
      s += this._content.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._constraints);
      s += ")";
      return s;
    }
    private static readonly RAST._ITypeParamDecl theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IType>.Empty);
    public static RAST._ITypeParamDecl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITypeParamDecl> _TYPE = new Dafny.TypeDescriptor<RAST._ITypeParamDecl>(RAST.TypeParamDecl.Default());
    public static Dafny.TypeDescriptor<RAST._ITypeParamDecl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITypeParamDecl create(Dafny.ISequence<Dafny.Rune> content, Dafny.ISequence<RAST._IType> constraints) {
      return new TypeParamDecl(content, constraints);
    }
    public static _ITypeParamDecl create_TypeParamDecl(Dafny.ISequence<Dafny.Rune> content, Dafny.ISequence<RAST._IType> constraints) {
      return create(content, constraints);
    }
    public bool is_TypeParamDecl { get { return true; } }
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
    public static Dafny.ISequence<Dafny.Rune> ToStringMultiple(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<Dafny.Rune> ind)
    {
      if ((new BigInteger((typeParams).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), RAST.__default.SeqToString<RAST._ITypeParamDecl>(typeParams, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._ITypeParamDecl, Dafny.ISequence<Dafny.Rune>>>>((_821_ind) => ((System.Func<RAST._ITypeParamDecl, Dafny.ISequence<Dafny.Rune>>)((_822_t) => {
          return (_822_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_821_ind, RAST.__default.IND));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
    }
    public static Dafny.ISequence<RAST._ITypeParamDecl> AddConstraintsMultiple(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IType> constraints)
    {
      Dafny.ISequence<RAST._ITypeParamDecl> _823___accumulator = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((typeParams).Count)).Sign == 0) {
        return Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_823___accumulator, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements());
      } else {
        _823___accumulator = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_823___accumulator, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(((typeParams).Select(BigInteger.Zero)).AddConstraints(constraints)));
        Dafny.ISequence<RAST._ITypeParamDecl> _in111 = (typeParams).Drop(BigInteger.One);
        Dafny.ISequence<RAST._IType> _in112 = constraints;
        typeParams = _in111;
        constraints = _in112;
        goto TAIL_CALL_START;
      }
    }
    public RAST._ITypeParamDecl AddConstraints(Dafny.ISequence<RAST._IType> constraints) {
      RAST._ITypeParamDecl _824_dt__update__tmp_h0 = this;
      Dafny.ISequence<RAST._IType> _825_dt__update_hconstraints_h0 = Dafny.Sequence<RAST._IType>.Concat((this).dtor_constraints, constraints);
      return RAST.TypeParamDecl.create((_824_dt__update__tmp_h0).dtor_content, _825_dt__update_hconstraints_h0);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_content, (((new BigInteger(((this).dtor_constraints).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), RAST.__default.SeqToString<RAST._IType>((this).dtor_constraints, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_826_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_827_t) => {
        return (_827_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_826_ind, RAST.__default.IND));
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
    bool is_Bool { get; }
    bool is_TIdentifier { get; }
    bool is_TMemberSelect { get; }
    bool is_TypeApp { get; }
    bool is_Borrowed { get; }
    bool is_BorrowedMut { get; }
    bool is_Pointer { get; }
    bool is_PointerMut { get; }
    bool is_ImplType { get; }
    bool is_DynType { get; }
    bool is_TupleType { get; }
    bool is_FnType { get; }
    bool is_IntersectionType { get; }
    bool is_Array { get; }
    bool is_TSynonym { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IType dtor_base { get; }
    RAST._IType dtor_baseName { get; }
    Dafny.ISequence<RAST._IType> dtor_arguments { get; }
    RAST._IType dtor_underlying { get; }
    RAST._IType dtor_returnType { get; }
    RAST._IType dtor_left { get; }
    RAST._IType dtor_right { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_size { get; }
    RAST._IType dtor_display { get; }
    _IType DowncastClone();
    RAST._IType Expand();
    bool EndsWithNameThatCanAcceptGenerics();
    RAST._IType Replace(Dafny.IMap<RAST._IType,RAST._IType> mapping);
    bool CanReadWithoutClone();
    bool IsSelfPointer();
    bool IsRcOrBorrowedRc();
    Std.Wrappers._IOption<RAST._IType> ExtractMaybePlacebo();
    Std.Wrappers._IOption<RAST._IType> ExtractMaybeUninitArrayElement();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
    RAST._IType MSel(Dafny.ISequence<Dafny.Rune> name);
    RAST._IType Apply1(RAST._IType arg);
    RAST._IType Apply(Dafny.ISequence<RAST._IType> args);
    RAST._IType ToOwned();
    RAST._IExpr ToNullExpr();
    bool IsMultiArray();
    Dafny.ISequence<Dafny.Rune> MultiArrayClass();
    RAST._IType MultiArrayUnderlying();
    RAST._IType TypeAtInitialization();
    bool IsMaybeUninit();
    bool IsUninitArray();
    bool IsObject();
    bool IsPointer();
    bool IsObjectOrPointer();
    RAST._IType ObjectOrPointerUnderlying();
    bool IsBuiltinCollection();
    RAST._IType GetBuiltinCollectionElement();
    bool IsRc();
    RAST._IType RcUnderlying();
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
    public static _IType create_Bool() {
      return new Type_Bool();
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
    public static _IType create_Pointer(RAST._IType underlying) {
      return new Type_Pointer(underlying);
    }
    public static _IType create_PointerMut(RAST._IType underlying) {
      return new Type_PointerMut(underlying);
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
    public static _IType create_Array(RAST._IType underlying, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> size) {
      return new Type_Array(underlying, size);
    }
    public static _IType create_TSynonym(RAST._IType display, RAST._IType @base) {
      return new Type_TSynonym(display, @base);
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
    public bool is_Bool { get { return this is Type_Bool; } }
    public bool is_TIdentifier { get { return this is Type_TIdentifier; } }
    public bool is_TMemberSelect { get { return this is Type_TMemberSelect; } }
    public bool is_TypeApp { get { return this is Type_TypeApp; } }
    public bool is_Borrowed { get { return this is Type_Borrowed; } }
    public bool is_BorrowedMut { get { return this is Type_BorrowedMut; } }
    public bool is_Pointer { get { return this is Type_Pointer; } }
    public bool is_PointerMut { get { return this is Type_PointerMut; } }
    public bool is_ImplType { get { return this is Type_ImplType; } }
    public bool is_DynType { get { return this is Type_DynType; } }
    public bool is_TupleType { get { return this is Type_TupleType; } }
    public bool is_FnType { get { return this is Type_FnType; } }
    public bool is_IntersectionType { get { return this is Type_IntersectionType; } }
    public bool is_Array { get { return this is Type_Array; } }
    public bool is_TSynonym { get { return this is Type_TSynonym; } }
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
        if (d is Type_TMemberSelect) { return ((Type_TMemberSelect)d)._base; }
        return ((Type_TSynonym)d)._base;
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
        if (d is Type_Pointer) { return ((Type_Pointer)d)._underlying; }
        if (d is Type_PointerMut) { return ((Type_PointerMut)d)._underlying; }
        if (d is Type_ImplType) { return ((Type_ImplType)d)._underlying; }
        if (d is Type_DynType) { return ((Type_DynType)d)._underlying; }
        return ((Type_Array)d)._underlying;
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
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_size {
      get {
        var d = this;
        return ((Type_Array)d)._size;
      }
    }
    public RAST._IType dtor_display {
      get {
        var d = this;
        return ((Type_TSynonym)d)._display;
      }
    }
    public abstract _IType DowncastClone();
    public RAST._IType Expand() {
      _IType _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_TSynonym) {
        RAST._IType _in113 = (_this).dtor_base;
        _this = _in113;
        ;
        goto TAIL_CALL_START;
      } else {
        return _this;
      }
    }
    public bool EndsWithNameThatCanAcceptGenerics() {
      return ((((((((((((((((((((this).is_U8) || ((this).is_U16)) || ((this).is_U32)) || ((this).is_U64)) || ((this).is_U128)) || ((this).is_I8)) || ((this).is_I16)) || ((this).is_I32)) || ((this).is_I64)) || ((this).is_I128)) || ((this).is_TIdentifier)) || ((this).is_TMemberSelect)) || (((this).is_Borrowed) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_BorrowedMut) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_Pointer) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_PointerMut) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_ImplType) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_DynType) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_IntersectionType) && (((this).dtor_right).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_TSynonym) && (((this).dtor_display).EndsWithNameThatCanAcceptGenerics()));
    }
    public RAST._IType Replace(Dafny.IMap<RAST._IType,RAST._IType> mapping) {
      var _pat_let_tv41 = mapping;
      var _pat_let_tv42 = mapping;
      var _pat_let_tv43 = mapping;
      var _pat_let_tv44 = mapping;
      var _pat_let_tv45 = mapping;
      var _pat_let_tv46 = mapping;
      var _pat_let_tv47 = mapping;
      var _pat_let_tv48 = mapping;
      var _pat_let_tv49 = mapping;
      var _pat_let_tv50 = mapping;
      var _pat_let_tv51 = mapping;
      var _pat_let_tv52 = mapping;
      var _pat_let_tv53 = mapping;
      var _pat_let_tv54 = mapping;
      var _pat_let_tv55 = mapping;
      var _pat_let_tv56 = mapping;
      var _pat_let_tv57 = mapping;
      if ((mapping).Contains(this)) {
        return Dafny.Map<RAST._IType, RAST._IType>.Select(mapping,this);
      } else {
        RAST._IType _source30 = this;
        bool unmatched30 = true;
        if (unmatched30) {
          if (_source30.is_SelfOwned) {
            unmatched30 = false;
            return this;
          }
        }
        if (unmatched30) {
          bool disjunctiveMatch1 = false;
          if (_source30.is_U8) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_U16) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_U32) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_U64) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_U128) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_I8) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_I16) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_I32) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_I64) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_I128) {
            disjunctiveMatch1 = true;
          }
          if (_source30.is_Bool) {
            disjunctiveMatch1 = true;
          }
          if (disjunctiveMatch1) {
            unmatched30 = false;
            return this;
          }
        }
        if (unmatched30) {
          if (_source30.is_TIdentifier) {
            unmatched30 = false;
            return this;
          }
        }
        if (unmatched30) {
          if (_source30.is_TMemberSelect) {
            RAST._IType _828_base = _source30.dtor_base;
            Dafny.ISequence<Dafny.Rune> _829_name = _source30.dtor_name;
            unmatched30 = false;
            RAST._IType _830_dt__update__tmp_h0 = this;
            RAST._IType _831_dt__update_hbase_h0 = (_828_base).Replace(_pat_let_tv41);
            if ((_830_dt__update__tmp_h0).is_TMemberSelect) {
              return RAST.Type.create_TMemberSelect(_831_dt__update_hbase_h0, (_830_dt__update__tmp_h0).dtor_name);
            } else {
              return RAST.Type.create_TSynonym((_830_dt__update__tmp_h0).dtor_display, _831_dt__update_hbase_h0);
            }
          }
        }
        if (unmatched30) {
          if (_source30.is_TypeApp) {
            RAST._IType _832_baseName = _source30.dtor_baseName;
            Dafny.ISequence<RAST._IType> _833_arguments = _source30.dtor_arguments;
            unmatched30 = false;
            RAST._IType _834_dt__update__tmp_h1 = this;
            Dafny.ISequence<RAST._IType> _835_dt__update_harguments_h0 = Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<RAST._IType,RAST._IType>, Dafny.ISequence<RAST._IType>, Func<RAST._IType, RAST._IType>>>((_836_mapping, _837_arguments) => ((System.Func<RAST._IType, RAST._IType>)((_838_t) => {
              return (_838_t).Replace(_836_mapping);
            })))(_pat_let_tv42, _833_arguments), _833_arguments);
            RAST._IType _839_dt__update_hbaseName_h0 = (_832_baseName).Replace(_pat_let_tv43);
            return RAST.Type.create_TypeApp(_839_dt__update_hbaseName_h0, _835_dt__update_harguments_h0);
          }
        }
        if (unmatched30) {
          if (_source30.is_Borrowed) {
            RAST._IType _840_underlying = _source30.dtor_underlying;
            unmatched30 = false;
            RAST._IType _841_dt__update__tmp_h2 = this;
            RAST._IType _842_dt__update_hunderlying_h0 = (_840_underlying).Replace(_pat_let_tv44);
            if ((_841_dt__update__tmp_h2).is_Borrowed) {
              return RAST.Type.create_Borrowed(_842_dt__update_hunderlying_h0);
            } else if ((_841_dt__update__tmp_h2).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_842_dt__update_hunderlying_h0);
            } else if ((_841_dt__update__tmp_h2).is_Pointer) {
              return RAST.Type.create_Pointer(_842_dt__update_hunderlying_h0);
            } else if ((_841_dt__update__tmp_h2).is_PointerMut) {
              return RAST.Type.create_PointerMut(_842_dt__update_hunderlying_h0);
            } else if ((_841_dt__update__tmp_h2).is_ImplType) {
              return RAST.Type.create_ImplType(_842_dt__update_hunderlying_h0);
            } else if ((_841_dt__update__tmp_h2).is_DynType) {
              return RAST.Type.create_DynType(_842_dt__update_hunderlying_h0);
            } else {
              return RAST.Type.create_Array(_842_dt__update_hunderlying_h0, (_841_dt__update__tmp_h2).dtor_size);
            }
          }
        }
        if (unmatched30) {
          if (_source30.is_BorrowedMut) {
            RAST._IType _843_underlying = _source30.dtor_underlying;
            unmatched30 = false;
            RAST._IType _844_dt__update__tmp_h3 = this;
            RAST._IType _845_dt__update_hunderlying_h1 = (_843_underlying).Replace(_pat_let_tv45);
            if ((_844_dt__update__tmp_h3).is_Borrowed) {
              return RAST.Type.create_Borrowed(_845_dt__update_hunderlying_h1);
            } else if ((_844_dt__update__tmp_h3).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_845_dt__update_hunderlying_h1);
            } else if ((_844_dt__update__tmp_h3).is_Pointer) {
              return RAST.Type.create_Pointer(_845_dt__update_hunderlying_h1);
            } else if ((_844_dt__update__tmp_h3).is_PointerMut) {
              return RAST.Type.create_PointerMut(_845_dt__update_hunderlying_h1);
            } else if ((_844_dt__update__tmp_h3).is_ImplType) {
              return RAST.Type.create_ImplType(_845_dt__update_hunderlying_h1);
            } else if ((_844_dt__update__tmp_h3).is_DynType) {
              return RAST.Type.create_DynType(_845_dt__update_hunderlying_h1);
            } else {
              return RAST.Type.create_Array(_845_dt__update_hunderlying_h1, (_844_dt__update__tmp_h3).dtor_size);
            }
          }
        }
        if (unmatched30) {
          if (_source30.is_Pointer) {
            RAST._IType _846_underlying = _source30.dtor_underlying;
            unmatched30 = false;
            RAST._IType _847_dt__update__tmp_h4 = this;
            RAST._IType _848_dt__update_hunderlying_h2 = (_846_underlying).Replace(_pat_let_tv46);
            if ((_847_dt__update__tmp_h4).is_Borrowed) {
              return RAST.Type.create_Borrowed(_848_dt__update_hunderlying_h2);
            } else if ((_847_dt__update__tmp_h4).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_848_dt__update_hunderlying_h2);
            } else if ((_847_dt__update__tmp_h4).is_Pointer) {
              return RAST.Type.create_Pointer(_848_dt__update_hunderlying_h2);
            } else if ((_847_dt__update__tmp_h4).is_PointerMut) {
              return RAST.Type.create_PointerMut(_848_dt__update_hunderlying_h2);
            } else if ((_847_dt__update__tmp_h4).is_ImplType) {
              return RAST.Type.create_ImplType(_848_dt__update_hunderlying_h2);
            } else if ((_847_dt__update__tmp_h4).is_DynType) {
              return RAST.Type.create_DynType(_848_dt__update_hunderlying_h2);
            } else {
              return RAST.Type.create_Array(_848_dt__update_hunderlying_h2, (_847_dt__update__tmp_h4).dtor_size);
            }
          }
        }
        if (unmatched30) {
          if (_source30.is_PointerMut) {
            RAST._IType _849_underlying = _source30.dtor_underlying;
            unmatched30 = false;
            RAST._IType _850_dt__update__tmp_h5 = this;
            RAST._IType _851_dt__update_hunderlying_h3 = (_849_underlying).Replace(_pat_let_tv47);
            if ((_850_dt__update__tmp_h5).is_Borrowed) {
              return RAST.Type.create_Borrowed(_851_dt__update_hunderlying_h3);
            } else if ((_850_dt__update__tmp_h5).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_851_dt__update_hunderlying_h3);
            } else if ((_850_dt__update__tmp_h5).is_Pointer) {
              return RAST.Type.create_Pointer(_851_dt__update_hunderlying_h3);
            } else if ((_850_dt__update__tmp_h5).is_PointerMut) {
              return RAST.Type.create_PointerMut(_851_dt__update_hunderlying_h3);
            } else if ((_850_dt__update__tmp_h5).is_ImplType) {
              return RAST.Type.create_ImplType(_851_dt__update_hunderlying_h3);
            } else if ((_850_dt__update__tmp_h5).is_DynType) {
              return RAST.Type.create_DynType(_851_dt__update_hunderlying_h3);
            } else {
              return RAST.Type.create_Array(_851_dt__update_hunderlying_h3, (_850_dt__update__tmp_h5).dtor_size);
            }
          }
        }
        if (unmatched30) {
          if (_source30.is_ImplType) {
            RAST._IType _852_underlying = _source30.dtor_underlying;
            unmatched30 = false;
            RAST._IType _853_dt__update__tmp_h6 = this;
            RAST._IType _854_dt__update_hunderlying_h4 = (_852_underlying).Replace(_pat_let_tv48);
            if ((_853_dt__update__tmp_h6).is_Borrowed) {
              return RAST.Type.create_Borrowed(_854_dt__update_hunderlying_h4);
            } else if ((_853_dt__update__tmp_h6).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_854_dt__update_hunderlying_h4);
            } else if ((_853_dt__update__tmp_h6).is_Pointer) {
              return RAST.Type.create_Pointer(_854_dt__update_hunderlying_h4);
            } else if ((_853_dt__update__tmp_h6).is_PointerMut) {
              return RAST.Type.create_PointerMut(_854_dt__update_hunderlying_h4);
            } else if ((_853_dt__update__tmp_h6).is_ImplType) {
              return RAST.Type.create_ImplType(_854_dt__update_hunderlying_h4);
            } else if ((_853_dt__update__tmp_h6).is_DynType) {
              return RAST.Type.create_DynType(_854_dt__update_hunderlying_h4);
            } else {
              return RAST.Type.create_Array(_854_dt__update_hunderlying_h4, (_853_dt__update__tmp_h6).dtor_size);
            }
          }
        }
        if (unmatched30) {
          if (_source30.is_DynType) {
            RAST._IType _855_underlying = _source30.dtor_underlying;
            unmatched30 = false;
            RAST._IType _856_dt__update__tmp_h7 = this;
            RAST._IType _857_dt__update_hunderlying_h5 = (_855_underlying).Replace(_pat_let_tv49);
            if ((_856_dt__update__tmp_h7).is_Borrowed) {
              return RAST.Type.create_Borrowed(_857_dt__update_hunderlying_h5);
            } else if ((_856_dt__update__tmp_h7).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_857_dt__update_hunderlying_h5);
            } else if ((_856_dt__update__tmp_h7).is_Pointer) {
              return RAST.Type.create_Pointer(_857_dt__update_hunderlying_h5);
            } else if ((_856_dt__update__tmp_h7).is_PointerMut) {
              return RAST.Type.create_PointerMut(_857_dt__update_hunderlying_h5);
            } else if ((_856_dt__update__tmp_h7).is_ImplType) {
              return RAST.Type.create_ImplType(_857_dt__update_hunderlying_h5);
            } else if ((_856_dt__update__tmp_h7).is_DynType) {
              return RAST.Type.create_DynType(_857_dt__update_hunderlying_h5);
            } else {
              return RAST.Type.create_Array(_857_dt__update_hunderlying_h5, (_856_dt__update__tmp_h7).dtor_size);
            }
          }
        }
        if (unmatched30) {
          if (_source30.is_TupleType) {
            Dafny.ISequence<RAST._IType> _858_arguments = _source30.dtor_arguments;
            unmatched30 = false;
            RAST._IType _859_dt__update__tmp_h8 = this;
            Dafny.ISequence<RAST._IType> _860_dt__update_harguments_h1 = Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<RAST._IType,RAST._IType>, Dafny.ISequence<RAST._IType>, Func<RAST._IType, RAST._IType>>>((_861_mapping, _862_arguments) => ((System.Func<RAST._IType, RAST._IType>)((_863_t) => {
              return (_863_t).Replace(_861_mapping);
            })))(_pat_let_tv50, _858_arguments), _858_arguments);
            if ((_859_dt__update__tmp_h8).is_TypeApp) {
              return RAST.Type.create_TypeApp((_859_dt__update__tmp_h8).dtor_baseName, _860_dt__update_harguments_h1);
            } else if ((_859_dt__update__tmp_h8).is_TupleType) {
              return RAST.Type.create_TupleType(_860_dt__update_harguments_h1);
            } else {
              return RAST.Type.create_FnType(_860_dt__update_harguments_h1, (_859_dt__update__tmp_h8).dtor_returnType);
            }
          }
        }
        if (unmatched30) {
          if (_source30.is_FnType) {
            Dafny.ISequence<RAST._IType> _864_arguments = _source30.dtor_arguments;
            RAST._IType _865_returnType = _source30.dtor_returnType;
            unmatched30 = false;
            RAST._IType _866_dt__update__tmp_h9 = this;
            RAST._IType _867_dt__update_hreturnType_h0 = (_865_returnType).Replace(_pat_let_tv51);
            Dafny.ISequence<RAST._IType> _868_dt__update_harguments_h2 = Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<RAST._IType,RAST._IType>, Dafny.ISequence<RAST._IType>, Func<RAST._IType, RAST._IType>>>((_869_mapping, _870_arguments) => ((System.Func<RAST._IType, RAST._IType>)((_871_t) => {
              return (_871_t).Replace(_869_mapping);
            })))(_pat_let_tv52, _864_arguments), _864_arguments);
            return RAST.Type.create_FnType(_868_dt__update_harguments_h2, _867_dt__update_hreturnType_h0);
          }
        }
        if (unmatched30) {
          if (_source30.is_IntersectionType) {
            RAST._IType _872_left = _source30.dtor_left;
            RAST._IType _873_right = _source30.dtor_right;
            unmatched30 = false;
            RAST._IType _874_dt__update__tmp_h10 = this;
            RAST._IType _875_dt__update_hright_h0 = (_873_right).Replace(_pat_let_tv53);
            RAST._IType _876_dt__update_hleft_h0 = (_872_left).Replace(_pat_let_tv54);
            return RAST.Type.create_IntersectionType(_876_dt__update_hleft_h0, _875_dt__update_hright_h0);
          }
        }
        if (unmatched30) {
          if (_source30.is_Array) {
            RAST._IType _877_underlying = _source30.dtor_underlying;
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _878_size = _source30.dtor_size;
            unmatched30 = false;
            RAST._IType _879_dt__update__tmp_h11 = this;
            RAST._IType _880_dt__update_hunderlying_h6 = (_877_underlying).Replace(_pat_let_tv55);
            if ((_879_dt__update__tmp_h11).is_Borrowed) {
              return RAST.Type.create_Borrowed(_880_dt__update_hunderlying_h6);
            } else if ((_879_dt__update__tmp_h11).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_880_dt__update_hunderlying_h6);
            } else if ((_879_dt__update__tmp_h11).is_Pointer) {
              return RAST.Type.create_Pointer(_880_dt__update_hunderlying_h6);
            } else if ((_879_dt__update__tmp_h11).is_PointerMut) {
              return RAST.Type.create_PointerMut(_880_dt__update_hunderlying_h6);
            } else if ((_879_dt__update__tmp_h11).is_ImplType) {
              return RAST.Type.create_ImplType(_880_dt__update_hunderlying_h6);
            } else if ((_879_dt__update__tmp_h11).is_DynType) {
              return RAST.Type.create_DynType(_880_dt__update_hunderlying_h6);
            } else {
              return RAST.Type.create_Array(_880_dt__update_hunderlying_h6, (_879_dt__update__tmp_h11).dtor_size);
            }
          }
        }
        if (unmatched30) {
          RAST._IType _881_display = _source30.dtor_display;
          RAST._IType _882_base = _source30.dtor_base;
          unmatched30 = false;
          RAST._IType _883_dt__update__tmp_h12 = this;
          RAST._IType _884_dt__update_hbase_h1 = (_882_base).Replace(_pat_let_tv56);
          RAST._IType _885_dt__update_hdisplay_h0 = (_881_display).Replace(_pat_let_tv57);
          return RAST.Type.create_TSynonym(_885_dt__update_hdisplay_h0, _884_dt__update_hbase_h1);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public bool CanReadWithoutClone() {
      return ((((((((((((((this).is_U8) || ((this).is_U16)) || ((this).is_U32)) || ((this).is_U64)) || ((this).is_U128)) || ((this).is_I8)) || ((this).is_I16)) || ((this).is_I32)) || ((this).is_I64)) || ((this).is_I128)) || ((this).is_Bool)) || ((this).is_Pointer)) || ((this).is_PointerMut)) || (((this).is_TSynonym) && (((this).dtor_base).CanReadWithoutClone()));
    }
    public bool IsSelfPointer() {
      return ((((((this).is_Borrowed) && (((this).dtor_underlying).is_PointerMut)) && ((((this).dtor_underlying).dtor_underlying).is_SelfOwned)) || (((this).is_PointerMut) && (((this).dtor_underlying).is_SelfOwned))) || (((((this).is_PointerMut) && (((this).dtor_underlying).is_TypeApp)) && ((new BigInteger((((this).dtor_underlying).dtor_arguments).Count)).Sign == 0)) && ((((this).dtor_underlying).dtor_baseName).is_SelfOwned))) || (((this).is_TSynonym) && (((this).dtor_base).IsSelfPointer()));
    }
    public bool IsRcOrBorrowedRc() {
      return ((((this).is_TypeApp) && (object.Equals((this).dtor_baseName, RAST.__default.RcType))) || (((this).is_Borrowed) && (((this).dtor_underlying).IsRcOrBorrowedRc()))) || (((this).is_TSynonym) && (((this).dtor_base).IsRcOrBorrowedRc()));
    }
    public Std.Wrappers._IOption<RAST._IType> ExtractMaybePlacebo() {
      RAST._IType _source31 = this;
      bool unmatched31 = true;
      if (unmatched31) {
        if (_source31.is_TypeApp) {
          RAST._IType _886_wrapper = _source31.dtor_baseName;
          Dafny.ISequence<RAST._IType> _887_arguments = _source31.dtor_arguments;
          unmatched31 = false;
          if (((object.Equals(_886_wrapper, RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo")))) || (object.Equals(_886_wrapper, (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))))) && ((new BigInteger((_887_arguments).Count)) == (BigInteger.One))) {
            return Std.Wrappers.Option<RAST._IType>.create_Some((_887_arguments).Select(BigInteger.Zero));
          } else {
            return Std.Wrappers.Option<RAST._IType>.create_None();
          }
        }
      }
      if (unmatched31) {
        unmatched31 = false;
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
      throw new System.Exception("unexpected control point");
    }
    public Std.Wrappers._IOption<RAST._IType> ExtractMaybeUninitArrayElement() {
      if ((this).IsObjectOrPointer()) {
        RAST._IType _888_s = (this).ObjectOrPointerUnderlying();
        if (((_888_s).is_Array) && (RAST.__default.IsMaybeUninitType((_888_s).dtor_underlying))) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.MaybeUninitTypeUnderlying((_888_s).dtor_underlying));
        } else if (((_888_s).IsMultiArray()) && (RAST.__default.IsMaybeUninitType((_888_s).MultiArrayUnderlying()))) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.MaybeUninitTypeUnderlying((_888_s).MultiArrayUnderlying()));
        } else {
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      } else {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
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
      RAST._IType _source32 = this;
      bool unmatched32 = true;
      if (unmatched32) {
        if (_source32.is_Bool) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool");
        }
      }
      if (unmatched32) {
        if (_source32.is_TIdentifier) {
          Dafny.ISequence<Dafny.Rune> _889_underlying = _source32.dtor_name;
          unmatched32 = false;
          return _889_underlying;
        }
      }
      if (unmatched32) {
        if (_source32.is_TMemberSelect) {
          RAST._IType _890_underlying = _source32.dtor_base;
          Dafny.ISequence<Dafny.Rune> _891_name = _source32.dtor_name;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_890_underlying)._ToString(_pat_let_tv58), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _891_name);
        }
      }
      if (unmatched32) {
        if (_source32.is_Borrowed) {
          RAST._IType _892_underlying = _source32.dtor_underlying;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), (_892_underlying)._ToString(_pat_let_tv59));
        }
      }
      if (unmatched32) {
        if (_source32.is_BorrowedMut) {
          RAST._IType _893_underlying = _source32.dtor_underlying;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut "), (_893_underlying)._ToString(_pat_let_tv60));
        }
      }
      if (unmatched32) {
        if (_source32.is_Pointer) {
          RAST._IType _894_underlying = _source32.dtor_underlying;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*const "), (_894_underlying)._ToString(_pat_let_tv61));
        }
      }
      if (unmatched32) {
        if (_source32.is_PointerMut) {
          RAST._IType _895_underlying = _source32.dtor_underlying;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*mut "), (_895_underlying)._ToString(_pat_let_tv62));
        }
      }
      if (unmatched32) {
        if (_source32.is_ImplType) {
          RAST._IType _896_underlying = _source32.dtor_underlying;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), (_896_underlying)._ToString(_pat_let_tv63));
        }
      }
      if (unmatched32) {
        if (_source32.is_DynType) {
          RAST._IType _897_underlying = _source32.dtor_underlying;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn "), (_897_underlying)._ToString(_pat_let_tv64));
        }
      }
      if (unmatched32) {
        if (_source32.is_FnType) {
          Dafny.ISequence<RAST._IType> _898_arguments = _source32.dtor_arguments;
          RAST._IType _899_returnType = _source32.dtor_returnType;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Fn("), RAST.__default.SeqToString<RAST._IType>(_898_arguments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_900_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_901_arg) => {
            return (_901_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_900_ind, RAST.__default.IND));
          })))(_pat_let_tv65), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), (_899_returnType)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv66, RAST.__default.IND)));
        }
      }
      if (unmatched32) {
        if (_source32.is_IntersectionType) {
          RAST._IType _902_left = _source32.dtor_left;
          RAST._IType _903_right = _source32.dtor_right;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_902_left)._ToString(_pat_let_tv67), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + ")), (_903_right)._ToString(_pat_let_tv68));
        }
      }
      if (unmatched32) {
        if (_source32.is_TupleType) {
          Dafny.ISequence<RAST._IType> _904_args = _source32.dtor_arguments;
          unmatched32 = false;
          if ((_904_args).Equals(Dafny.Sequence<RAST._IType>.FromElements())) {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()");
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._IType>(_904_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_905_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_906_arg) => {
              return (_906_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_905_ind, RAST.__default.IND));
            })))(_pat_let_tv69), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
        }
      }
      if (unmatched32) {
        if (_source32.is_TypeApp) {
          RAST._IType _907_base = _source32.dtor_baseName;
          Dafny.ISequence<RAST._IType> _908_args = _source32.dtor_arguments;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat((_907_base)._ToString(_pat_let_tv70), (((_908_args).Equals(Dafny.Sequence<RAST._IType>.FromElements())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), RAST.__default.SeqToString<RAST._IType>(_908_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_909_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_910_arg) => {
            return (_910_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_909_ind, RAST.__default.IND));
          })))(_pat_let_tv71), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">")))));
        }
      }
      if (unmatched32) {
        if (_source32.is_SelfOwned) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
        }
      }
      if (unmatched32) {
        if (_source32.is_U8) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8");
        }
      }
      if (unmatched32) {
        if (_source32.is_U16) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16");
        }
      }
      if (unmatched32) {
        if (_source32.is_U32) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32");
        }
      }
      if (unmatched32) {
        if (_source32.is_U64) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64");
        }
      }
      if (unmatched32) {
        if (_source32.is_U128) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128");
        }
      }
      if (unmatched32) {
        if (_source32.is_I8) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8");
        }
      }
      if (unmatched32) {
        if (_source32.is_I16) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16");
        }
      }
      if (unmatched32) {
        if (_source32.is_I32) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32");
        }
      }
      if (unmatched32) {
        if (_source32.is_I64) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64");
        }
      }
      if (unmatched32) {
        if (_source32.is_I128) {
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128");
        }
      }
      if (unmatched32) {
        if (_source32.is_Array) {
          RAST._IType _911_underlying = _source32.dtor_underlying;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _912_size = _source32.dtor_size;
          unmatched32 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("["), (_911_underlying)._ToString(_pat_let_tv72)), (((_912_size).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; "), (_912_size).dtor_value)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
        }
      }
      if (unmatched32) {
        RAST._IType _913_display = _source32.dtor_display;
        RAST._IType _914_base = _source32.dtor_base;
        unmatched32 = false;
        return (_913_display)._ToString(_pat_let_tv73);
      }
      throw new System.Exception("unexpected control point");
    }
    public RAST._IType MSel(Dafny.ISequence<Dafny.Rune> name) {
      return RAST.Type.create_TMemberSelect(this, name);
    }
    public RAST._IType Apply1(RAST._IType arg) {
      return RAST.Type.create_TypeApp(this, Dafny.Sequence<RAST._IType>.FromElements(arg));
    }
    public RAST._IType Apply(Dafny.ISequence<RAST._IType> args) {
      return RAST.Type.create_TypeApp(this, args);
    }
    public RAST._IType ToOwned() {
      RAST._IType _source33 = this;
      bool unmatched33 = true;
      if (unmatched33) {
        if (_source33.is_Borrowed) {
          RAST._IType _915_x = _source33.dtor_underlying;
          unmatched33 = false;
          return _915_x;
        }
      }
      if (unmatched33) {
        if (_source33.is_BorrowedMut) {
          RAST._IType _916_x = _source33.dtor_underlying;
          unmatched33 = false;
          return _916_x;
        }
      }
      if (unmatched33) {
        RAST._IType _917_x = _source33;
        unmatched33 = false;
        return _917_x;
      }
      throw new System.Exception("unexpected control point");
    }
    public RAST._IExpr ToNullExpr() {
      if (((this).Expand()).IsObject()) {
        return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")));
      } else {
        RAST._IType _918_underlying = ((this).Expand()).dtor_underlying;
        Dafny.ISequence<Dafny.Rune> _919_n = ((((this).Expand()).is_PointerMut) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null_mut")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null")));
        if (((_918_underlying).is_Array) && (((_918_underlying).dtor_size).is_None)) {
          return ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(_919_n)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Array((_918_underlying).dtor_underlying, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        } else {
          return (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(_919_n)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        }
      }
    }
    public bool IsMultiArray() {
      RAST._IType _920_t = (this).Expand();
      return ((_920_t).is_TypeApp) && (Dafny.Helpers.Let<RAST._IType, bool>((_920_t).dtor_baseName, _pat_let5_0 => Dafny.Helpers.Let<RAST._IType, bool>(_pat_let5_0, _921_baseName => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, bool>((_920_t).dtor_arguments, _pat_let6_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, bool>(_pat_let6_0, _922_args => (((((new BigInteger((_922_args).Count)) == (BigInteger.One)) && ((_921_baseName).is_TMemberSelect)) && (object.Equals((_921_baseName).dtor_base, RAST.__default.dafny__runtime__type))) && ((new BigInteger(((_921_baseName).dtor_name).Count)) >= (new BigInteger(5)))) && ((((_921_baseName).dtor_name).Subsequence(BigInteger.Zero, new BigInteger(5))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"))))))));
    }
    public Dafny.ISequence<Dafny.Rune> MultiArrayClass() {
      return (((this).Expand()).dtor_baseName).dtor_name;
    }
    public RAST._IType MultiArrayUnderlying() {
      return (((this).Expand()).dtor_arguments).Select(BigInteger.Zero);
    }
    public RAST._IType TypeAtInitialization() {
      if ((this).IsObjectOrPointer()) {
        RAST._IType _923_s = (this).ObjectOrPointerUnderlying();
        if (((_923_s).is_Array) && (((_923_s).dtor_size).is_None)) {
          RAST._IType _924_newUnderlying = RAST.Type.create_Array(RAST.__default.MaybeUninitType((_923_s).dtor_underlying), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
          if ((this).IsObject()) {
            return RAST.__default.ObjectType(_924_newUnderlying);
          } else {
            return RAST.Type.create_PointerMut(_924_newUnderlying);
          }
        } else if ((_923_s).IsMultiArray()) {
          RAST._IType _925_newUnderlying = RAST.Type.create_TypeApp(((_923_s).Expand()).dtor_baseName, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.MaybeUninitType((((_923_s).Expand()).dtor_arguments).Select(BigInteger.Zero))));
          if ((this).IsObject()) {
            return RAST.__default.ObjectType(_925_newUnderlying);
          } else {
            return RAST.Type.create_PointerMut(_925_newUnderlying);
          }
        } else {
          return this;
        }
      } else {
        return this;
      }
    }
    public bool IsMaybeUninit() {
      return (((this).is_TypeApp) && (object.Equals((this).dtor_baseName, RAST.__default.MaybeUninitPath))) && ((new BigInteger(((this).dtor_arguments).Count)) == (BigInteger.One));
    }
    public bool IsUninitArray() {
      if ((this).IsObjectOrPointer()) {
        RAST._IType _926_s = ((this).ObjectOrPointerUnderlying()).Expand();
        if (((_926_s).is_Array) && (((_926_s).dtor_size).is_None)) {
          return ((_926_s).dtor_underlying).IsMaybeUninit();
        } else if ((_926_s).IsMultiArray()) {
          return (((_926_s).dtor_arguments).Select(BigInteger.Zero)).IsMaybeUninit();
        } else {
          return false;
        }
      } else {
        return false;
      }
    }
    public bool IsObject() {
      RAST._IType _source34 = this;
      bool unmatched34 = true;
      if (unmatched34) {
        if (_source34.is_TypeApp) {
          RAST._IType baseName0 = _source34.dtor_baseName;
          if (baseName0.is_TMemberSelect) {
            RAST._IType base0 = baseName0.dtor_base;
            if (base0.is_TMemberSelect) {
              RAST._IType base1 = base0.dtor_base;
              if (base1.is_TIdentifier) {
                Dafny.ISequence<Dafny.Rune> name0 = base1.dtor_name;
                if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                  Dafny.ISequence<Dafny.Rune> name1 = base0.dtor_name;
                  if (object.Equals(name1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime"))) {
                    Dafny.ISequence<Dafny.Rune> name2 = baseName0.dtor_name;
                    if (object.Equals(name2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))) {
                      Dafny.ISequence<RAST._IType> _927_elems1 = _source34.dtor_arguments;
                      unmatched34 = false;
                      return (new BigInteger((_927_elems1).Count)) == (BigInteger.One);
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched34) {
        unmatched34 = false;
        return false;
      }
      throw new System.Exception("unexpected control point");
    }
    public bool IsPointer() {
      return ((this).is_Pointer) || ((this).is_PointerMut);
    }
    public bool IsObjectOrPointer()
    {
      bool _hresult = false;
      RAST._IType _928_t;
      _928_t = (this).Expand();
      _hresult = ((_928_t).IsPointer()) || ((_928_t).IsObject());
      return _hresult;
      return _hresult;
    }
    public RAST._IType ObjectOrPointerUnderlying()
    {
      RAST._IType _hresult = RAST.Type.Default();
      RAST._IType _929_t;
      _929_t = (this).Expand();
      if ((_929_t).IsPointer()) {
        _hresult = (_929_t).dtor_underlying;
        return _hresult;
      }
      _hresult = ((_929_t).dtor_arguments).Select(BigInteger.Zero);
      return _hresult;
      return _hresult;
    }
    public bool IsBuiltinCollection() {
      RAST._IType _source35 = (this).Expand();
      bool unmatched35 = true;
      if (unmatched35) {
        if (_source35.is_TypeApp) {
          RAST._IType baseName1 = _source35.dtor_baseName;
          if (baseName1.is_TMemberSelect) {
            RAST._IType base2 = baseName1.dtor_base;
            if (base2.is_TMemberSelect) {
              RAST._IType base3 = base2.dtor_base;
              if (base3.is_TIdentifier) {
                Dafny.ISequence<Dafny.Rune> name3 = base3.dtor_name;
                if (object.Equals(name3, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                  Dafny.ISequence<Dafny.Rune> name4 = base2.dtor_name;
                  if (object.Equals(name4, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime"))) {
                    Dafny.ISequence<Dafny.Rune> _930_tpe = baseName1.dtor_name;
                    Dafny.ISequence<RAST._IType> _931_elems1 = _source35.dtor_arguments;
                    unmatched35 = false;
                    return (((((_930_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))) || ((_930_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")))) || ((_930_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")))) && ((new BigInteger((_931_elems1).Count)) == (BigInteger.One))) || (((_930_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) && ((new BigInteger((_931_elems1).Count)) == (new BigInteger(2))));
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched35) {
        unmatched35 = false;
        return false;
      }
      throw new System.Exception("unexpected control point");
    }
    public RAST._IType GetBuiltinCollectionElement() {
      RAST._IType _source36 = (this).Expand();
      bool unmatched36 = true;
      if (unmatched36) {
        RAST._IType baseName2 = _source36.dtor_baseName;
        RAST._IType base4 = baseName2.dtor_base;
        RAST._IType base5 = base4.dtor_base;
        Dafny.ISequence<Dafny.Rune> name5 = base5.dtor_name;
        if (object.Equals(name5, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
          Dafny.ISequence<Dafny.Rune> name6 = base4.dtor_name;
          if (object.Equals(name6, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime"))) {
            Dafny.ISequence<Dafny.Rune> _932_tpe = baseName2.dtor_name;
            Dafny.ISequence<RAST._IType> _933_elems = _source36.dtor_arguments;
            unmatched36 = false;
            if ((_932_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) {
              return (_933_elems).Select(BigInteger.One);
            } else {
              return (_933_elems).Select(BigInteger.Zero);
            }
          }
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public bool IsRc() {
      return (((this).is_TypeApp) && (object.Equals((this).dtor_baseName, RAST.__default.RcType))) && ((new BigInteger(((this).dtor_arguments).Count)) == (BigInteger.One));
    }
    public RAST._IType RcUnderlying() {
      return ((this).dtor_arguments).Select(BigInteger.Zero);
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
  public class Type_Bool : Type {
    public Type_Bool() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Bool();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_Bool;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.Bool";
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
      hash = ((hash << 5) + hash) + 12;
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
      hash = ((hash << 5) + hash) + 13;
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
      hash = ((hash << 5) + hash) + 14;
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
      hash = ((hash << 5) + hash) + 15;
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
      hash = ((hash << 5) + hash) + 16;
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
  public class Type_Pointer : Type {
    public readonly RAST._IType _underlying;
    public Type_Pointer(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Pointer(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_Pointer;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.Pointer";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Type_PointerMut : Type {
    public readonly RAST._IType _underlying;
    public Type_PointerMut(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_PointerMut(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_PointerMut;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.PointerMut";
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
      hash = ((hash << 5) + hash) + 19;
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
      hash = ((hash << 5) + hash) + 20;
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
      hash = ((hash << 5) + hash) + 21;
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
      hash = ((hash << 5) + hash) + 22;
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
      hash = ((hash << 5) + hash) + 23;
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
  public class Type_Array : Type {
    public readonly RAST._IType _underlying;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _size;
    public Type_Array(RAST._IType underlying, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> size) : base() {
      this._underlying = underlying;
      this._size = size;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Array(_underlying, _size);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_Array;
      return oth != null && object.Equals(this._underlying, oth._underlying) && object.Equals(this._size, oth._size);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._size));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ", ";
      s += Dafny.Helpers.ToString(this._size);
      s += ")";
      return s;
    }
  }
  public class Type_TSynonym : Type {
    public readonly RAST._IType _display;
    public readonly RAST._IType _base;
    public Type_TSynonym(RAST._IType display, RAST._IType @base) : base() {
      this._display = display;
      this._base = @base;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TSynonym(_display, _base);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TSynonym;
      return oth != null && object.Equals(this._display, oth._display) && object.Equals(this._base, oth._base);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 25;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._display));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._base));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TSynonym";
      s += "(";
      s += Dafny.Helpers.ToString(this._display);
      s += ", ";
      s += Dafny.Helpers.ToString(this._base);
      s += ")";
      return s;
    }
  }

  public interface _ITrait {
    bool is_Trait { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    RAST._IType dtor_tpe { get; }
    Dafny.ISequence<RAST._IType> dtor_parents { get; }
    Dafny.ISequence<RAST._IImplMember> dtor_body { get; }
    _ITrait DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Trait : _ITrait {
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IType _tpe;
    public readonly Dafny.ISequence<RAST._IType> _parents;
    public readonly Dafny.ISequence<RAST._IImplMember> _body;
    public Trait(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<RAST._IType> parents, Dafny.ISequence<RAST._IImplMember> body) {
      this._typeParams = typeParams;
      this._tpe = tpe;
      this._parents = parents;
      this._body = body;
    }
    public _ITrait DowncastClone() {
      if (this is _ITrait dt) { return dt; }
      return new Trait(_typeParams, _tpe, _parents, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Trait;
      return oth != null && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._parents, oth._parents) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._parents));
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
      s += Dafny.Helpers.ToString(this._parents);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
    private static readonly RAST._ITrait theDefault = create(Dafny.Sequence<RAST._ITypeParamDecl>.Empty, RAST.Type.Default(), Dafny.Sequence<RAST._IType>.Empty, Dafny.Sequence<RAST._IImplMember>.Empty);
    public static RAST._ITrait Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITrait> _TYPE = new Dafny.TypeDescriptor<RAST._ITrait>(RAST.Trait.Default());
    public static Dafny.TypeDescriptor<RAST._ITrait> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITrait create(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<RAST._IType> parents, Dafny.ISequence<RAST._IImplMember> body) {
      return new Trait(typeParams, tpe, parents, body);
    }
    public static _ITrait create_Trait(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<RAST._IType> parents, Dafny.ISequence<RAST._IImplMember> body) {
      return create(typeParams, tpe, parents, body);
    }
    public bool is_Trait { get { return true; } }
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_parents {
      get {
        return this._parents;
      }
    }
    public Dafny.ISequence<RAST._IImplMember> dtor_body {
      get {
        return this._body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      Dafny.ISequence<RAST._ITypeParamDecl> _934_tpConstraints = Std.Collections.Seq.__default.Filter<RAST._ITypeParamDecl>(((System.Func<RAST._ITypeParamDecl, bool>)((_935_typeParamDecl) => {
        return (new BigInteger(((_935_typeParamDecl).dtor_constraints).Count)).Sign == 1;
      })), (this).dtor_typeParams);
      Dafny.ISequence<Dafny.Rune> _936_additionalConstraints = RAST.__default.SeqToString<RAST._ITypeParamDecl>(_934_tpConstraints, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._ITypeParamDecl, Dafny.ISequence<Dafny.Rune>>>>((_937_ind) => ((System.Func<RAST._ITypeParamDecl, Dafny.ISequence<Dafny.Rune>>)((_938_t) => {
        return (_938_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_937_ind, RAST.__default.IND));
      })))(ind), Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _939_parents = (((new BigInteger(((this).dtor_parents).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), RAST.__default.SeqToString<RAST._IType>((this).dtor_parents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_940_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_941_t) => {
        return (_941_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_940_ind, RAST.__default.IND));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + ")))));
      Dafny.ISequence<Dafny.Rune> _942_where = (((_936_additionalConstraints).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where\n")), ind), RAST.__default.IND), _936_additionalConstraints)));
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub trait "), ((this).dtor_tpe)._ToString(ind)), _939_parents), _942_where), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IImplMember>((this).dtor_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>>>((_943_ind) => ((System.Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>)((_944_member) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _943_ind), RAST.__default.IND), (_944_member)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_943_ind, RAST.__default.IND)));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (((new BigInteger(((this).dtor_body).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }

  public interface _IImpl {
    bool is_ImplFor { get; }
    bool is_Impl { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
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
    private static readonly RAST._IImpl theDefault = create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.Empty, RAST.Type.Default(), RAST.Type.Default(), Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IImplMember>.Empty);
    public static RAST._IImpl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IImpl> _TYPE = new Dafny.TypeDescriptor<RAST._IImpl>(RAST.Impl.Default());
    public static Dafny.TypeDescriptor<RAST._IImpl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImpl create_ImplFor(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, RAST._IType forType, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) {
      return new Impl_ImplFor(typeParams, tpe, forType, @where, body);
    }
    public static _IImpl create_Impl(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) {
      return new Impl_Impl(typeParams, tpe, @where, body);
    }
    public bool is_ImplFor { get { return this is Impl_ImplFor; } }
    public bool is_Impl { get { return this is Impl_Impl; } }
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
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
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), ((this).dtor_tpe)._ToString(ind)), (((this).is_ImplFor) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for ")), ((this).dtor_forType)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), ((!((this).dtor_where).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), (this).dtor_where)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IImplMember>((this).dtor_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>>>((_945_ind) => ((System.Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>)((_946_member) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _945_ind), RAST.__default.IND), (_946_member)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_945_ind, RAST.__default.IND)));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (((new BigInteger(((this).dtor_body).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }
  public class Impl_ImplFor : Impl {
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IType _tpe;
    public readonly RAST._IType _forType;
    public readonly Dafny.ISequence<Dafny.Rune> _where;
    public readonly Dafny.ISequence<RAST._IImplMember> _body;
    public Impl_ImplFor(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, RAST._IType forType, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) : base() {
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
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IType _tpe;
    public readonly Dafny.ISequence<Dafny.Rune> _where;
    public readonly Dafny.ISequence<RAST._IImplMember> _body;
    public Impl_Impl(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<Dafny.Rune> @where, Dafny.ISequence<RAST._IImplMember> body) : base() {
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
    bool is_ImplMemberMacro { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
    RAST._IVisibility dtor_pub { get; }
    RAST._IFn dtor_fun { get; }
    RAST._IExpr dtor_expr { get; }
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
    public static _IImplMember create_ImplMemberMacro(RAST._IExpr expr) {
      return new ImplMember_ImplMemberMacro(expr);
    }
    public bool is_RawImplMember { get { return this is ImplMember_RawImplMember; } }
    public bool is_FnDecl { get { return this is ImplMember_FnDecl; } }
    public bool is_ImplMemberMacro { get { return this is ImplMember_ImplMemberMacro; } }
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
    public RAST._IExpr dtor_expr {
      get {
        var d = this;
        return ((ImplMember_ImplMemberMacro)d)._expr;
      }
    }
    public abstract _IImplMember DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      if ((this).is_FnDecl) {
        return Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_pub)._ToString(), ((this).dtor_fun)._ToString(ind));
      } else if ((this).is_ImplMemberMacro) {
        return Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_expr)._ToString(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
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
  public class ImplMember_ImplMemberMacro : ImplMember {
    public readonly RAST._IExpr _expr;
    public ImplMember_ImplMemberMacro(RAST._IExpr expr) : base() {
      this._expr = expr;
    }
    public override _IImplMember DowncastClone() {
      if (this is _IImplMember dt) { return dt; }
      return new ImplMember_ImplMemberMacro(_expr);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ImplMember_ImplMemberMacro;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ImplMember.ImplMemberMacro";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ")";
      return s;
    }
  }

  public interface _IVisibility {
    bool is_PUB { get; }
    bool is_PRIV { get; }
    _IVisibility DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString();
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
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      if ((this).is_PUB) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub ");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      }
    }
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
      if ((((this).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) && (object.Equals((this).dtor_tpe, RAST.Type.create_SelfOwned()))) {
        return (this).dtor_name;
      } else if ((((this).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) && (object.Equals((this).dtor_tpe, RAST.__default.SelfBorrowed))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), (this).dtor_name);
      } else if ((((this).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) && (object.Equals((this).dtor_tpe, RAST.__default.SelfBorrowedMut))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut "), (this).dtor_name);
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((this).dtor_tpe)._ToString(ind));
      }
    }
    public static RAST._IFormal selfBorrowed { get {
      return RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.__default.SelfBorrowed);
    } }
    public static RAST._IFormal selfOwned { get {
      return RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.Type.create_SelfOwned());
    } }
    public static RAST._IFormal selfBorrowedMut { get {
      return RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.__default.SelfBorrowedMut);
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
      Dafny.ISequence<Dafny.Rune> _947_newIndent = ((((this).dtor_rhs).is_Block) ? (ind) : (Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)));
      Dafny.ISequence<Dafny.Rune> _948_rhsString = ((this).dtor_rhs)._ToString(_947_newIndent);
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Pattern._ToString((this).dtor_pattern, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" =>")), ((((_948_rhsString).Contains(new Dafny.Rune('\n'))) && (((_948_rhsString).Select(BigInteger.Zero)) != (new Dafny.Rune('{')))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), _948_rhsString)) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), _948_rhsString))));
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

  public interface _IAssignLhs {
    bool is_LocalVar { get; }
    bool is_SelectMember { get; }
    bool is_ExtractTuple { get; }
    bool is_Index { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IExpr dtor_on { get; }
    Dafny.ISequence<Dafny.Rune> dtor_field { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_names { get; }
    RAST._IExpr dtor_expr { get; }
    Dafny.ISequence<RAST._IExpr> dtor_indices { get; }
    _IAssignLhs DowncastClone();
  }
  public abstract class AssignLhs : _IAssignLhs {
    public AssignLhs() {
    }
    private static readonly RAST._IAssignLhs theDefault = create_LocalVar(Dafny.Sequence<Dafny.Rune>.Empty);
    public static RAST._IAssignLhs Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IAssignLhs> _TYPE = new Dafny.TypeDescriptor<RAST._IAssignLhs>(RAST.AssignLhs.Default());
    public static Dafny.TypeDescriptor<RAST._IAssignLhs> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAssignLhs create_LocalVar(Dafny.ISequence<Dafny.Rune> name) {
      return new AssignLhs_LocalVar(name);
    }
    public static _IAssignLhs create_SelectMember(RAST._IExpr @on, Dafny.ISequence<Dafny.Rune> field) {
      return new AssignLhs_SelectMember(@on, field);
    }
    public static _IAssignLhs create_ExtractTuple(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names) {
      return new AssignLhs_ExtractTuple(names);
    }
    public static _IAssignLhs create_Index(RAST._IExpr expr, Dafny.ISequence<RAST._IExpr> indices) {
      return new AssignLhs_Index(expr, indices);
    }
    public bool is_LocalVar { get { return this is AssignLhs_LocalVar; } }
    public bool is_SelectMember { get { return this is AssignLhs_SelectMember; } }
    public bool is_ExtractTuple { get { return this is AssignLhs_ExtractTuple; } }
    public bool is_Index { get { return this is AssignLhs_Index; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((AssignLhs_LocalVar)d)._name;
      }
    }
    public RAST._IExpr dtor_on {
      get {
        var d = this;
        return ((AssignLhs_SelectMember)d)._on;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_field {
      get {
        var d = this;
        return ((AssignLhs_SelectMember)d)._field;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_names {
      get {
        var d = this;
        return ((AssignLhs_ExtractTuple)d)._names;
      }
    }
    public RAST._IExpr dtor_expr {
      get {
        var d = this;
        return ((AssignLhs_Index)d)._expr;
      }
    }
    public Dafny.ISequence<RAST._IExpr> dtor_indices {
      get {
        var d = this;
        return ((AssignLhs_Index)d)._indices;
      }
    }
    public abstract _IAssignLhs DowncastClone();
  }
  public class AssignLhs_LocalVar : AssignLhs {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public AssignLhs_LocalVar(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_LocalVar(_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignLhs_LocalVar;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignLhs.LocalVar";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_SelectMember : AssignLhs {
    public readonly RAST._IExpr _on;
    public readonly Dafny.ISequence<Dafny.Rune> _field;
    public AssignLhs_SelectMember(RAST._IExpr @on, Dafny.ISequence<Dafny.Rune> field) : base() {
      this._on = @on;
      this._field = field;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_SelectMember(_on, _field);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignLhs_SelectMember;
      return oth != null && object.Equals(this._on, oth._on) && object.Equals(this._field, oth._field);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._field));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignLhs.SelectMember";
      s += "(";
      s += Dafny.Helpers.ToString(this._on);
      s += ", ";
      s += this._field.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_ExtractTuple : AssignLhs {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _names;
    public AssignLhs_ExtractTuple(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names) : base() {
      this._names = names;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_ExtractTuple(_names);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignLhs_ExtractTuple;
      return oth != null && object.Equals(this._names, oth._names);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._names));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignLhs.ExtractTuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._names);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_Index : AssignLhs {
    public readonly RAST._IExpr _expr;
    public readonly Dafny.ISequence<RAST._IExpr> _indices;
    public AssignLhs_Index(RAST._IExpr expr, Dafny.ISequence<RAST._IExpr> indices) : base() {
      this._expr = expr;
      this._indices = indices;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Index(_expr, _indices);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignLhs_Index;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._indices, oth._indices);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._indices));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignLhs.Index";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._indices);
      s += ")";
      return s;
    }
  }

  public interface _IExpr {
    bool is_RawExpr { get; }
    bool is_ExprFromType { get; }
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
    bool is_LiteralBool { get; }
    bool is_LiteralString { get; }
    bool is_DeclareVar { get; }
    bool is_Assign { get; }
    bool is_IfExpr { get; }
    bool is_Loop { get; }
    bool is_For { get; }
    bool is_Labelled { get; }
    bool is_Break { get; }
    bool is_Continue { get; }
    bool is_Return { get; }
    bool is_CallType { get; }
    bool is_Call { get; }
    bool is_Select { get; }
    bool is_SelectIndex { get; }
    bool is_MemberSelect { get; }
    bool is_Lambda { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
    RAST._IType dtor_tpe { get; }
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
    Dafny.ISequence<Dafny.Rune> dtor_value { get; }
    bool dtor_bvalue { get; }
    bool dtor_binary { get; }
    bool dtor_verbatim { get; }
    RAST._IDeclareType dtor_declareType { get; }
    Std.Wrappers._IOption<RAST._IType> dtor_optType { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_optRhs { get; }
    Std.Wrappers._IOption<RAST._IAssignLhs> dtor_names { get; }
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
    Dafny.ISequence<RAST._IFormal> dtor_params { get; }
    Std.Wrappers._IOption<RAST._IType> dtor_retType { get; }
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
    RAST._IExpr ApplyType(Dafny.ISequence<RAST._IType> typeParameters);
    RAST._IExpr ApplyType1(RAST._IType typeParameter);
    RAST._IExpr Apply(Dafny.ISequence<RAST._IExpr> arguments);
    RAST._IExpr Apply1(RAST._IExpr argument);
    bool IsLhsIdentifier();
    Dafny.ISequence<Dafny.Rune> LhsIdentifierName();
    RAST._IExpr Clone();
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
    public static _IExpr create_ExprFromType(RAST._IType tpe) {
      return new Expr_ExprFromType(tpe);
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
    public static _IExpr create_StructBuild(RAST._IExpr underlying, Dafny.ISequence<RAST._IAssignIdentifier> assignments) {
      return new Expr_StructBuild(underlying, assignments);
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
    public static _IExpr create_LiteralBool(bool bvalue) {
      return new Expr_LiteralBool(bvalue);
    }
    public static _IExpr create_LiteralString(Dafny.ISequence<Dafny.Rune> @value, bool binary, bool verbatim) {
      return new Expr_LiteralString(@value, binary, verbatim);
    }
    public static _IExpr create_DeclareVar(RAST._IDeclareType declareType, Dafny.ISequence<Dafny.Rune> name, Std.Wrappers._IOption<RAST._IType> optType, Std.Wrappers._IOption<RAST._IExpr> optRhs) {
      return new Expr_DeclareVar(declareType, name, optType, optRhs);
    }
    public static _IExpr create_Assign(Std.Wrappers._IOption<RAST._IAssignLhs> names, RAST._IExpr rhs) {
      return new Expr_Assign(names, rhs);
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
    public static _IExpr create_CallType(RAST._IExpr obj, Dafny.ISequence<RAST._IType> typeParameters) {
      return new Expr_CallType(obj, typeParameters);
    }
    public static _IExpr create_Call(RAST._IExpr obj, Dafny.ISequence<RAST._IExpr> arguments) {
      return new Expr_Call(obj, arguments);
    }
    public static _IExpr create_Select(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) {
      return new Expr_Select(obj, name);
    }
    public static _IExpr create_SelectIndex(RAST._IExpr obj, RAST._IExpr range) {
      return new Expr_SelectIndex(obj, range);
    }
    public static _IExpr create_MemberSelect(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) {
      return new Expr_MemberSelect(obj, name);
    }
    public static _IExpr create_Lambda(Dafny.ISequence<RAST._IFormal> @params, Std.Wrappers._IOption<RAST._IType> retType, RAST._IExpr body) {
      return new Expr_Lambda(@params, retType, body);
    }
    public bool is_RawExpr { get { return this is Expr_RawExpr; } }
    public bool is_ExprFromType { get { return this is Expr_ExprFromType; } }
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
    public bool is_LiteralBool { get { return this is Expr_LiteralBool; } }
    public bool is_LiteralString { get { return this is Expr_LiteralString; } }
    public bool is_DeclareVar { get { return this is Expr_DeclareVar; } }
    public bool is_Assign { get { return this is Expr_Assign; } }
    public bool is_IfExpr { get { return this is Expr_IfExpr; } }
    public bool is_Loop { get { return this is Expr_Loop; } }
    public bool is_For { get { return this is Expr_For; } }
    public bool is_Labelled { get { return this is Expr_Labelled; } }
    public bool is_Break { get { return this is Expr_Break; } }
    public bool is_Continue { get { return this is Expr_Continue; } }
    public bool is_Return { get { return this is Expr_Return; } }
    public bool is_CallType { get { return this is Expr_CallType; } }
    public bool is_Call { get { return this is Expr_Call; } }
    public bool is_Select { get { return this is Expr_Select; } }
    public bool is_SelectIndex { get { return this is Expr_SelectIndex; } }
    public bool is_MemberSelect { get { return this is Expr_MemberSelect; } }
    public bool is_Lambda { get { return this is Expr_Lambda; } }
    public Dafny.ISequence<Dafny.Rune> dtor_content {
      get {
        var d = this;
        return ((Expr_RawExpr)d)._content;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        var d = this;
        if (d is Expr_ExprFromType) { return ((Expr_ExprFromType)d)._tpe; }
        return ((Expr_TypeAscription)d)._tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Expr_Identifier) { return ((Expr_Identifier)d)._name; }
        if (d is Expr_DeclareVar) { return ((Expr_DeclareVar)d)._name; }
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
        return ((Expr_Assign)d)._rhs;
      }
    }
    public RAST._IExpr dtor_underlying {
      get {
        var d = this;
        if (d is Expr_Block) { return ((Expr_Block)d)._underlying; }
        if (d is Expr_StructBuild) { return ((Expr_StructBuild)d)._underlying; }
        if (d is Expr_UnaryOp) { return ((Expr_UnaryOp)d)._underlying; }
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
    public Dafny.ISequence<Dafny.Rune> dtor_value {
      get {
        var d = this;
        if (d is Expr_LiteralInt) { return ((Expr_LiteralInt)d)._value; }
        return ((Expr_LiteralString)d)._value;
      }
    }
    public bool dtor_bvalue {
      get {
        var d = this;
        return ((Expr_LiteralBool)d)._bvalue;
      }
    }
    public bool dtor_binary {
      get {
        var d = this;
        return ((Expr_LiteralString)d)._binary;
      }
    }
    public bool dtor_verbatim {
      get {
        var d = this;
        return ((Expr_LiteralString)d)._verbatim;
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
    public Std.Wrappers._IOption<RAST._IAssignLhs> dtor_names {
      get {
        var d = this;
        return ((Expr_Assign)d)._names;
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
        if (d is Expr_For) { return ((Expr_For)d)._range; }
        return ((Expr_SelectIndex)d)._range;
      }
    }
    public RAST._IExpr dtor_body {
      get {
        var d = this;
        if (d is Expr_For) { return ((Expr_For)d)._body; }
        return ((Expr_Lambda)d)._body;
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
        if (d is Expr_CallType) { return ((Expr_CallType)d)._obj; }
        if (d is Expr_Call) { return ((Expr_Call)d)._obj; }
        if (d is Expr_Select) { return ((Expr_Select)d)._obj; }
        if (d is Expr_SelectIndex) { return ((Expr_SelectIndex)d)._obj; }
        return ((Expr_MemberSelect)d)._obj;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_typeParameters {
      get {
        var d = this;
        return ((Expr_CallType)d)._typeParameters;
      }
    }
    public Dafny.ISequence<RAST._IFormal> dtor_params {
      get {
        var d = this;
        return ((Expr_Lambda)d)._params;
      }
    }
    public Std.Wrappers._IOption<RAST._IType> dtor_retType {
      get {
        var d = this;
        return ((Expr_Lambda)d)._retType;
      }
    }
    public abstract _IExpr DowncastClone();
    public bool NoExtraSemicolonAfter() {
      return (((((((this).is_DeclareVar) || ((this).is_Assign)) || ((this).is_Break)) || ((this).is_Continue)) || ((this).is_Return)) || ((this).is_For)) || ((((this).is_RawExpr) && ((new BigInteger(((this).dtor_content).Count)).Sign == 1)) && ((((this).dtor_content).Select((new BigInteger(((this).dtor_content).Count)) - (BigInteger.One))) == (new Dafny.Rune(';'))));
    }
    public RAST._IExpr Optimize() {
      RAST._IExpr _source37 = this;
      bool unmatched37 = true;
      if (unmatched37) {
        if (_source37.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> op10 = _source37.dtor_op1;
          if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"))) {
            RAST._IExpr underlying0 = _source37.dtor_underlying;
            if (underlying0.is_BinaryOp) {
              Dafny.ISequence<Dafny.Rune> op20 = underlying0.dtor_op2;
              if (object.Equals(op20, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
                RAST._IExpr _949_left = underlying0.dtor_left;
                RAST._IExpr _950_right = underlying0.dtor_right;
                DAST.Format._IBinaryOpFormat _951_format = underlying0.dtor_format2;
                DAST.Format._IUnaryOpFormat format0 = _source37.dtor_format;
                if (format0.is_CombineFormat) {
                  unmatched37 = false;
                  return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="), _949_left, _950_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            }
          }
        }
      }
      if (unmatched37) {
        if (_source37.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> op11 = _source37.dtor_op1;
          if (object.Equals(op11, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"))) {
            RAST._IExpr underlying1 = _source37.dtor_underlying;
            if (underlying1.is_BinaryOp) {
              Dafny.ISequence<Dafny.Rune> op21 = underlying1.dtor_op2;
              if (object.Equals(op21, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
                RAST._IExpr _952_left = underlying1.dtor_left;
                RAST._IExpr _953_right = underlying1.dtor_right;
                DAST.Format._IBinaryOpFormat format20 = underlying1.dtor_format2;
                if (format20.is_NoFormat) {
                  DAST.Format._IUnaryOpFormat format1 = _source37.dtor_format;
                  if (format1.is_CombineFormat) {
                    unmatched37 = false;
                    return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="), _952_left, _953_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched37) {
        if (_source37.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> op12 = _source37.dtor_op1;
          if (object.Equals(op12, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"))) {
            RAST._IExpr underlying2 = _source37.dtor_underlying;
            if (underlying2.is_BinaryOp) {
              Dafny.ISequence<Dafny.Rune> op22 = underlying2.dtor_op2;
              if (object.Equals(op22, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
                RAST._IExpr _954_left = underlying2.dtor_left;
                RAST._IExpr _955_right = underlying2.dtor_right;
                DAST.Format._IBinaryOpFormat format21 = underlying2.dtor_format2;
                if (format21.is_ReverseFormat) {
                  DAST.Format._IUnaryOpFormat format2 = _source37.dtor_format;
                  if (format2.is_CombineFormat) {
                    unmatched37 = false;
                    return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _955_right, _954_left, DAST.Format.BinaryOpFormat.create_NoFormat());
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched37) {
        if (_source37.is_Call) {
          RAST._IExpr obj0 = _source37.dtor_obj;
          if (obj0.is_MemberSelect) {
            RAST._IExpr _956_r = obj0.dtor_obj;
            Dafny.ISequence<Dafny.Rune> name7 = obj0.dtor_name;
            if (object.Equals(name7, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))) {
              Dafny.ISequence<RAST._IExpr> _957_args = _source37.dtor_arguments;
              unmatched37 = false;
              if (((!object.Equals(_956_r, RAST.__default.dafny__runtime)) && (!object.Equals(_956_r, RAST.__default.@global))) || ((new BigInteger((_957_args).Count)) != (new BigInteger(2)))) {
                return this;
              } else {
                RAST._IExpr _958_expr = (_957_args).Select(BigInteger.Zero);
                RAST._IExpr _959_tpeExpr = (_957_args).Select(BigInteger.One);
                if (!((_959_tpeExpr).is_ExprFromType)) {
                  return this;
                } else {
                  RAST._IType _960_tpe = (_959_tpeExpr).dtor_tpe;
                  if (((((((((((_960_tpe).is_U8) || ((_960_tpe).is_U16)) || ((_960_tpe).is_U32)) || ((_960_tpe).is_U64)) || ((_960_tpe).is_U128)) || ((_960_tpe).is_I8)) || ((_960_tpe).is_I16)) || ((_960_tpe).is_I32)) || ((_960_tpe).is_I64)) || ((_960_tpe).is_I128)) {
                    RAST._IExpr _source38 = _958_expr;
                    bool unmatched38 = true;
                    if (unmatched38) {
                      if (_source38.is_Call) {
                        RAST._IExpr obj1 = _source38.dtor_obj;
                        if (obj1.is_MemberSelect) {
                          RAST._IExpr _961_base = obj1.dtor_obj;
                          Dafny.ISequence<Dafny.Rune> name8 = obj1.dtor_name;
                          if (object.Equals(name8, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))) {
                            Dafny.ISequence<RAST._IExpr> _962_args = _source38.dtor_arguments;
                            unmatched38 = false;
                            if (((new BigInteger((_962_args).Count)) == (BigInteger.One)) && ((object.Equals(_961_base, RAST.__default.dafny__runtime)) || (object.Equals(_961_base, RAST.__default.@global)))) {
                              RAST._IExpr _source39 = (_962_args).Select(BigInteger.Zero);
                              bool unmatched39 = true;
                              if (unmatched39) {
                                if (_source39.is_LiteralInt) {
                                  Dafny.ISequence<Dafny.Rune> _963_number = _source39.dtor_value;
                                  unmatched39 = false;
                                  return RAST.Expr.create_LiteralInt(_963_number);
                                }
                              }
                              if (unmatched39) {
                                if (_source39.is_LiteralString) {
                                  Dafny.ISequence<Dafny.Rune> _964_number = _source39.dtor_value;
                                  unmatched39 = false;
                                  return RAST.Expr.create_LiteralInt(_964_number);
                                }
                              }
                              if (unmatched39) {
                                unmatched39 = false;
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
                    if (unmatched38) {
                      unmatched38 = false;
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
      if (unmatched37) {
        if (_source37.is_StmtExpr) {
          RAST._IExpr stmt0 = _source37.dtor_stmt;
          if (stmt0.is_DeclareVar) {
            RAST._IDeclareType _965_mod = stmt0.dtor_declareType;
            Dafny.ISequence<Dafny.Rune> _966_name = stmt0.dtor_name;
            Std.Wrappers._IOption<RAST._IType> optType0 = stmt0.dtor_optType;
            if (optType0.is_Some) {
              RAST._IType _967_tpe = optType0.dtor_value;
              Std.Wrappers._IOption<RAST._IExpr> optRhs0 = stmt0.dtor_optRhs;
              if (optRhs0.is_None) {
                RAST._IExpr rhs0 = _source37.dtor_rhs;
                if (rhs0.is_StmtExpr) {
                  RAST._IExpr stmt1 = rhs0.dtor_stmt;
                  if (stmt1.is_Assign) {
                    Std.Wrappers._IOption<RAST._IAssignLhs> _968_name2 = stmt1.dtor_names;
                    RAST._IExpr _969_rhs = stmt1.dtor_rhs;
                    RAST._IExpr _970_last = rhs0.dtor_rhs;
                    unmatched37 = false;
                    if (object.Equals(_968_name2, Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_LocalVar(_966_name)))) {
                      RAST._IExpr _971_rewriting = RAST.Expr.create_StmtExpr(RAST.Expr.create_DeclareVar(_965_mod, _966_name, Std.Wrappers.Option<RAST._IType>.create_Some(_967_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_969_rhs)), _970_last);
                      return _971_rewriting;
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
      if (unmatched37) {
        if (_source37.is_StmtExpr) {
          RAST._IExpr stmt2 = _source37.dtor_stmt;
          if (stmt2.is_IfExpr) {
            RAST._IExpr cond0 = stmt2.dtor_cond;
            if (cond0.is_UnaryOp) {
              Dafny.ISequence<Dafny.Rune> op13 = cond0.dtor_op1;
              if (object.Equals(op13, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"))) {
                RAST._IExpr underlying3 = cond0.dtor_underlying;
                if (underlying3.is_BinaryOp) {
                  Dafny.ISequence<Dafny.Rune> op23 = underlying3.dtor_op2;
                  if (object.Equals(op23, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
                    RAST._IExpr _972_a = underlying3.dtor_left;
                    RAST._IExpr _973_b = underlying3.dtor_right;
                    DAST.Format._IBinaryOpFormat _974_f = underlying3.dtor_format2;
                    DAST.Format._IUnaryOpFormat _975_of = cond0.dtor_format;
                    RAST._IExpr thn0 = stmt2.dtor_thn;
                    if (thn0.is_RawExpr) {
                      Dafny.ISequence<Dafny.Rune> content0 = thn0.dtor_content;
                      if (object.Equals(content0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");"))) {
                        RAST._IExpr els0 = stmt2.dtor_els;
                        if (els0.is_RawExpr) {
                          Dafny.ISequence<Dafny.Rune> content1 = els0.dtor_content;
                          if (object.Equals(content1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                            RAST._IExpr _976_last = _source37.dtor_rhs;
                            unmatched37 = false;
                            RAST._IExpr _977_rewriting = RAST.Expr.create_StmtExpr((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("assert_eq!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_972_a, _973_b)), _976_last);
                            return _977_rewriting;
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
      if (unmatched37) {
        unmatched37 = false;
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
      RAST._IExpr _source40 = this;
      bool unmatched40 = true;
      if (unmatched40) {
        if (_source40.is_MemberSelect) {
          Dafny.ISequence<Dafny.Rune> _978_id = _source40.dtor_name;
          unmatched40 = false;
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_978_id);
        }
      }
      if (unmatched40) {
        unmatched40 = false;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      }
      throw new System.Exception("unexpected control point");
    }
    public static Dafny.ISequence<Dafny.Rune> MaxHashes(Dafny.ISequence<Dafny.Rune> s, Dafny.ISequence<Dafny.Rune> currentHashes, Dafny.ISequence<Dafny.Rune> mostHashes)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        if ((new BigInteger((currentHashes).Count)) < (new BigInteger((mostHashes).Count))) {
          return mostHashes;
        } else {
          return currentHashes;
        }
      } else if (((s).Subsequence(BigInteger.Zero, BigInteger.One)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#"))) {
        Dafny.ISequence<Dafny.Rune> _in114 = (s).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in115 = Dafny.Sequence<Dafny.Rune>.Concat(currentHashes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#"));
        Dafny.ISequence<Dafny.Rune> _in116 = mostHashes;
        s = _in114;
        currentHashes = _in115;
        mostHashes = _in116;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<Dafny.Rune> _in117 = (s).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in118 = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        Dafny.ISequence<Dafny.Rune> _in119 = (((new BigInteger((currentHashes).Count)) < (new BigInteger((mostHashes).Count))) ? (mostHashes) : (currentHashes));
        s = _in117;
        currentHashes = _in118;
        mostHashes = _in119;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> RemoveDoubleQuotes(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<Dafny.Rune> _979___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)) <= (BigInteger.One)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_979___accumulator, s);
      } else if (((s).Subsequence(BigInteger.Zero, new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@""""""))) {
        _979___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_979___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@""""));
        Dafny.ISequence<Dafny.Rune> _in120 = (s).Drop(new BigInteger(2));
        s = _in120;
        goto TAIL_CALL_START;
      } else {
        _979___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_979___accumulator, (s).Subsequence(BigInteger.Zero, BigInteger.One));
        Dafny.ISequence<Dafny.Rune> _in121 = (s).Drop(BigInteger.One);
        s = _in121;
        goto TAIL_CALL_START;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
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
      var _pat_let_tv87 = ind;
      var _pat_let_tv88 = ind;
      var _pat_let_tv89 = ind;
      var _pat_let_tv90 = ind;
      var _pat_let_tv91 = ind;
      var _pat_let_tv92 = ind;
      var _pat_let_tv93 = ind;
      var _pat_let_tv94 = ind;
      var _pat_let_tv95 = ind;
      var _pat_let_tv96 = ind;
      var _pat_let_tv97 = ind;
      var _pat_let_tv98 = ind;
      var _pat_let_tv99 = ind;
      var _pat_let_tv100 = ind;
      var _pat_let_tv101 = ind;
      var _pat_let_tv102 = ind;
      var _pat_let_tv103 = ind;
      var _pat_let_tv104 = ind;
      var _pat_let_tv105 = ind;
      var _pat_let_tv106 = ind;
      var _pat_let_tv107 = ind;
      var _pat_let_tv108 = ind;
      var _pat_let_tv109 = ind;
      var _pat_let_tv110 = ind;
      var _pat_let_tv111 = ind;
      var _pat_let_tv112 = ind;
      var _pat_let_tv113 = ind;
      var _pat_let_tv114 = ind;
      var _pat_let_tv115 = ind;
      var _pat_let_tv116 = ind;
      var _pat_let_tv117 = ind;
      var _pat_let_tv118 = ind;
      var _pat_let_tv119 = ind;
      var _pat_let_tv120 = ind;
      var _pat_let_tv121 = ind;
      var _pat_let_tv122 = ind;
      var _pat_let_tv123 = ind;
      var _pat_let_tv124 = ind;
      var _pat_let_tv125 = ind;
      var _pat_let_tv126 = ind;
      var _pat_let_tv127 = ind;
      var _pat_let_tv128 = ind;
      var _pat_let_tv129 = ind;
      var _pat_let_tv130 = ind;
      var _pat_let_tv131 = ind;
      var _pat_let_tv132 = ind;
      var _pat_let_tv133 = ind;
      var _pat_let_tv134 = ind;
      RAST._IExpr _source41 = (this).Optimize();
      bool unmatched41 = true;
      if (unmatched41) {
        if (_source41.is_Identifier) {
          Dafny.ISequence<Dafny.Rune> _980_name = _source41.dtor_name;
          unmatched41 = false;
          return _980_name;
        }
      }
      if (unmatched41) {
        if (_source41.is_ExprFromType) {
          RAST._IType _981_t = _source41.dtor_tpe;
          unmatched41 = false;
          return (_981_t)._ToString(_pat_let_tv74);
        }
      }
      if (unmatched41) {
        if (_source41.is_LiteralInt) {
          Dafny.ISequence<Dafny.Rune> _982_number = _source41.dtor_value;
          unmatched41 = false;
          return _982_number;
        }
      }
      if (unmatched41) {
        if (_source41.is_LiteralBool) {
          bool _983_b = _source41.dtor_bvalue;
          unmatched41 = false;
          if (_983_b) {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true");
          } else {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false");
          }
        }
      }
      if (unmatched41) {
        if (_source41.is_LiteralString) {
          Dafny.ISequence<Dafny.Rune> _984_characters = _source41.dtor_value;
          bool _985_binary = _source41.dtor_binary;
          bool _986_verbatim = _source41.dtor_verbatim;
          unmatched41 = false;
          Dafny.ISequence<Dafny.Rune> _987_hashes = ((_986_verbatim) ? (Dafny.Sequence<Dafny.Rune>.Concat(RAST.Expr.MaxHashes(_984_characters, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#"))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((_985_binary) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("b")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), ((_986_verbatim) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r"), _987_hashes)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\"")), ((_986_verbatim) ? (RAST.Expr.RemoveDoubleQuotes(_984_characters)) : (_984_characters))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\"")), _987_hashes);
        }
      }
      if (unmatched41) {
        if (_source41.is_Match) {
          RAST._IExpr _988_matchee = _source41.dtor_matchee;
          Dafny.ISequence<RAST._IMatchCase> _989_cases = _source41.dtor_cases;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match "), (_988_matchee)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv75, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IMatchCase>(_989_cases, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IMatchCase, Dafny.ISequence<Dafny.Rune>>>>((_990_ind) => ((System.Func<RAST._IMatchCase, Dafny.ISequence<Dafny.Rune>>)((_991_c) => {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _990_ind), RAST.__default.IND), (_991_c)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_990_ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
          })))(_pat_let_tv76), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv77), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched41) {
        if (_source41.is_StmtExpr) {
          RAST._IExpr _992_stmt = _source41.dtor_stmt;
          RAST._IExpr _993_rhs = _source41.dtor_rhs;
          unmatched41 = false;
          if (((_992_stmt).is_RawExpr) && (((_992_stmt).dtor_content).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
            return (_993_rhs)._ToString(_pat_let_tv78);
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_992_stmt)._ToString(_pat_let_tv79), (((_992_stmt).NoExtraSemicolonAfter()) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv80), (_993_rhs)._ToString(_pat_let_tv81));
          }
        }
      }
      if (unmatched41) {
        if (_source41.is_Block) {
          RAST._IExpr _994_underlying = _source41.dtor_underlying;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n"), _pat_let_tv82), RAST.__default.IND), (_994_underlying)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv83, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv84), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched41) {
        if (_source41.is_IfExpr) {
          RAST._IExpr _995_cond = _source41.dtor_cond;
          RAST._IExpr _996_thn = _source41.dtor_thn;
          RAST._IExpr _997_els = _source41.dtor_els;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), (_995_cond)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv85, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _pat_let_tv86), RAST.__default.IND), (_996_thn)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv87, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv88), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")), ((object.Equals(_997_els, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" else {\n"), _pat_let_tv89), RAST.__default.IND), (_997_els)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv90, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv91), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        }
      }
      if (unmatched41) {
        if (_source41.is_StructBuild) {
          RAST._IExpr _998_name = _source41.dtor_underlying;
          Dafny.ISequence<RAST._IAssignIdentifier> _999_assignments = _source41.dtor_assignments;
          unmatched41 = false;
          if (((new BigInteger((_999_assignments).Count)).Sign == 1) && ((((_999_assignments).Select(BigInteger.Zero)).dtor_identifier).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_998_name)._ToString(_pat_let_tv92), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" (")), RAST.__default.SeqToString<RAST._IAssignIdentifier>(_999_assignments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>>>((_1000_ind) => ((System.Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>)((_1001_assignment) => {
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _1000_ind), RAST.__default.IND), ((_1001_assignment).dtor_rhs)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1000_ind, RAST.__default.IND)));
            })))(_pat_let_tv93), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_999_assignments).Count)) > (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _pat_let_tv94)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_998_name)._ToString(_pat_let_tv95), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IAssignIdentifier>(_999_assignments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>>>((_1002_ind) => ((System.Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>)((_1003_assignment) => {
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _1002_ind), RAST.__default.IND), (_1003_assignment)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1002_ind, RAST.__default.IND)));
            })))(_pat_let_tv96), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_999_assignments).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _pat_let_tv97)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
        }
      }
      if (unmatched41) {
        if (_source41.is_Tuple) {
          Dafny.ISequence<RAST._IExpr> _1004_arguments = _source41.dtor_arguments;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._IExpr>(_1004_arguments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_1005_ind) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_1006_arg) => {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _1005_ind), RAST.__default.IND), (_1006_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1005_ind, RAST.__default.IND)));
          })))(_pat_let_tv98), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_1004_arguments).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _pat_let_tv99)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      }
      if (unmatched41) {
        if (_source41.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> _1007_op = _source41.dtor_op1;
          RAST._IExpr _1008_underlying = _source41.dtor_underlying;
          DAST.Format._IUnaryOpFormat _1009_format = _source41.dtor_format;
          unmatched41 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs41 = ((((this).printingInfo).NeedParenthesesFor((_1008_underlying).printingInfo)) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))) : (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
          Dafny.ISequence<Dafny.Rune> _1010_leftP = _let_tmp_rhs41.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1011_rightP = _let_tmp_rhs41.dtor__1;
          Dafny.ISequence<Dafny.Rune> _1012_leftOp = ((((_1007_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"))) && (!(_1010_leftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_1007_op, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))) : ((((_1007_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (_1007_op))));
          Dafny.ISequence<Dafny.Rune> _1013_rightOp = (((_1007_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) ? (_1007_op) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1012_leftOp, _1010_leftP), (_1008_underlying)._ToString(_pat_let_tv100)), _1011_rightP), _1013_rightOp);
        }
      }
      if (unmatched41) {
        if (_source41.is_TypeAscription) {
          RAST._IExpr _1014_left = _source41.dtor_left;
          RAST._IType _1015_tpe = _source41.dtor_tpe;
          unmatched41 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs42 = (this).LeftParentheses(_1014_left);
          Dafny.ISequence<Dafny.Rune> _1016_leftLeftP = _let_tmp_rhs42.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1017_leftRightP = _let_tmp_rhs42.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1016_leftLeftP, (_1014_left)._ToString(RAST.__default.IND)), _1017_leftRightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ")), (_1015_tpe)._ToString(RAST.__default.IND));
        }
      }
      if (unmatched41) {
        if (_source41.is_BinaryOp) {
          Dafny.ISequence<Dafny.Rune> _1018_op2 = _source41.dtor_op2;
          RAST._IExpr _1019_left = _source41.dtor_left;
          RAST._IExpr _1020_right = _source41.dtor_right;
          DAST.Format._IBinaryOpFormat _1021_format = _source41.dtor_format2;
          unmatched41 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs43 = (this).LeftParentheses(_1019_left);
          Dafny.ISequence<Dafny.Rune> _1022_leftLeftP = _let_tmp_rhs43.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1023_leftRighP = _let_tmp_rhs43.dtor__1;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs44 = (this).RightParentheses(_1020_right);
          Dafny.ISequence<Dafny.Rune> _1024_rightLeftP = _let_tmp_rhs44.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1025_rightRightP = _let_tmp_rhs44.dtor__1;
          Dafny.ISequence<Dafny.Rune> _1026_opRendered = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), _1018_op2), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
          Dafny.ISequence<Dafny.Rune> _1027_indLeft = (((_1022_leftLeftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv101, RAST.__default.IND)) : (_pat_let_tv102));
          Dafny.ISequence<Dafny.Rune> _1028_indRight = (((_1024_rightLeftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv103, RAST.__default.IND)) : (_pat_let_tv104));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1022_leftLeftP, (_1019_left)._ToString(_1027_indLeft)), _1023_leftRighP), _1026_opRendered), _1024_rightLeftP), (_1020_right)._ToString(_1028_indRight)), _1025_rightRightP);
        }
      }
      if (unmatched41) {
        if (_source41.is_DeclareVar) {
          RAST._IDeclareType _1029_declareType = _source41.dtor_declareType;
          Dafny.ISequence<Dafny.Rune> _1030_name = _source41.dtor_name;
          Std.Wrappers._IOption<RAST._IType> _1031_optType = _source41.dtor_optType;
          Std.Wrappers._IOption<RAST._IExpr> _1032_optExpr = _source41.dtor_optRhs;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let "), ((object.Equals(_1029_declareType, RAST.DeclareType.create_MUT())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut ")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _1030_name), (((_1031_optType).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), ((_1031_optType).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv105, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), (((_1032_optExpr).is_Some) ? (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((_1032_optExpr).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv106, RAST.__default.IND)), _pat_let7_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let7_0, _1033_optExprString => (((_1033_optExprString).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("= /*issue with empty RHS*/"), ((((_1032_optExpr).dtor_value).is_RawExpr) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty Raw expr")) : (((((_1032_optExpr).dtor_value).is_LiteralString) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty string literal")) : (((((_1032_optExpr).dtor_value).is_LiteralInt) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty int literal")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Another case"))))))))) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "), _1033_optExprString)))))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      if (unmatched41) {
        if (_source41.is_Assign) {
          Std.Wrappers._IOption<RAST._IAssignLhs> _1034_names = _source41.dtor_names;
          RAST._IExpr _1035_expr = _source41.dtor_rhs;
          unmatched41 = false;
          Dafny.ISequence<Dafny.Rune> _1036_lhs = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
            Std.Wrappers._IOption<RAST._IAssignLhs> _source42 = _1034_names;
            bool unmatched42 = true;
            if (unmatched42) {
              if (_source42.is_Some) {
                RAST._IAssignLhs value0 = _source42.dtor_value;
                if (value0.is_LocalVar) {
                  Dafny.ISequence<Dafny.Rune> _1037_name = value0.dtor_name;
                  unmatched42 = false;
                  return Dafny.Sequence<Dafny.Rune>.Concat(_1037_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
                }
              }
            }
            if (unmatched42) {
              if (_source42.is_Some) {
                RAST._IAssignLhs value1 = _source42.dtor_value;
                if (value1.is_SelectMember) {
                  RAST._IExpr _1038_member = value1.dtor_on;
                  Dafny.ISequence<Dafny.Rune> _1039_field = value1.dtor_field;
                  unmatched42 = false;
                  _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs45 = (RAST.Expr.create_Select(_1038_member, _1039_field)).LeftParentheses(_1038_member);
                  Dafny.ISequence<Dafny.Rune> _1040_leftP = _let_tmp_rhs45.dtor__0;
                  Dafny.ISequence<Dafny.Rune> _1041_rightP = _let_tmp_rhs45.dtor__1;
                  return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1040_leftP, (_1038_member)._ToString(_pat_let_tv107)), _1041_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1039_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
                }
              }
            }
            if (unmatched42) {
              if (_source42.is_Some) {
                RAST._IAssignLhs value2 = _source42.dtor_value;
                if (value2.is_ExtractTuple) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1042_names = value2.dtor_names;
                  unmatched42 = false;
                  return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1042_names, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1043_name) => {
                    return _1043_name;
                  })), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") = "));
                }
              }
            }
            if (unmatched42) {
              if (_source42.is_Some) {
                RAST._IAssignLhs value3 = _source42.dtor_value;
                if (value3.is_Index) {
                  RAST._IExpr _1044_e = value3.dtor_expr;
                  Dafny.ISequence<RAST._IExpr> _1045_indices = value3.dtor_indices;
                  unmatched42 = false;
                  _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs46 = (RAST.Expr.create_Call(_1044_e, _1045_indices)).LeftParentheses(_1044_e);
                  Dafny.ISequence<Dafny.Rune> _1046_leftP = _let_tmp_rhs46.dtor__0;
                  Dafny.ISequence<Dafny.Rune> _1047_rightP = _let_tmp_rhs46.dtor__1;
                  return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1046_leftP, (_1044_e)._ToString(_pat_let_tv108)), _1047_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[")), RAST.__default.SeqToString<RAST._IExpr>(_1045_indices, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_1048_ind) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_1049_index) => {
                    return (_1049_index)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1048_ind, RAST.__default.IND));
                  })))(_pat_let_tv109), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]["))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("] = "));
                }
              }
            }
            if (unmatched42) {
              unmatched42 = false;
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ = ");
            }
            throw new System.Exception("unexpected control point");
          }))();
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1036_lhs, (_1035_expr)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv110, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      if (unmatched41) {
        if (_source41.is_Labelled) {
          Dafny.ISequence<Dafny.Rune> _1050_name = _source41.dtor_lbl;
          RAST._IExpr _1051_underlying = _source41.dtor_underlying;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"), _1050_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_1051_underlying)._ToString(_pat_let_tv111));
        }
      }
      if (unmatched41) {
        if (_source41.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1052_optLbl = _source41.dtor_optLbl;
          unmatched41 = false;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source43 = _1052_optLbl;
          bool unmatched43 = true;
          if (unmatched43) {
            if (_source43.is_Some) {
              Dafny.ISequence<Dafny.Rune> _1053_lbl = _source43.dtor_value;
              unmatched43 = false;
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break '"), _1053_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          }
          if (unmatched43) {
            unmatched43 = false;
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;");
          }
          throw new System.Exception("unexpected control point");
        }
      }
      if (unmatched41) {
        if (_source41.is_Continue) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1054_optLbl = _source41.dtor_optLbl;
          unmatched41 = false;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source44 = _1054_optLbl;
          bool unmatched44 = true;
          if (unmatched44) {
            if (_source44.is_Some) {
              Dafny.ISequence<Dafny.Rune> _1055_lbl = _source44.dtor_value;
              unmatched44 = false;
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue '"), _1055_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          }
          if (unmatched44) {
            unmatched44 = false;
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue;");
          }
          throw new System.Exception("unexpected control point");
        }
      }
      if (unmatched41) {
        if (_source41.is_Loop) {
          Std.Wrappers._IOption<RAST._IExpr> _1056_optCond = _source41.dtor_optCond;
          RAST._IExpr _1057_underlying = _source41.dtor_underlying;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
            Std.Wrappers._IOption<RAST._IExpr> _source45 = _1056_optCond;
            bool unmatched45 = true;
            if (unmatched45) {
              if (_source45.is_None) {
                unmatched45 = false;
                return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop");
              }
            }
            if (unmatched45) {
              RAST._IExpr _1058_c = _source45.dtor_value;
              unmatched45 = false;
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), (_1058_c)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv112, RAST.__default.IND)));
            }
            throw new System.Exception("unexpected control point");
          }))(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _pat_let_tv113), RAST.__default.IND), (_1057_underlying)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv114, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv115), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched41) {
        if (_source41.is_For) {
          Dafny.ISequence<Dafny.Rune> _1059_name = _source41.dtor_name;
          RAST._IExpr _1060_range = _source41.dtor_range;
          RAST._IExpr _1061_body = _source41.dtor_body;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for "), _1059_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" in ")), (_1060_range)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv116, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _pat_let_tv117), RAST.__default.IND), (_1061_body)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv118, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv119), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      if (unmatched41) {
        if (_source41.is_Return) {
          Std.Wrappers._IOption<RAST._IExpr> _1062_optExpr = _source41.dtor_optExpr;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), (((_1062_optExpr).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), ((_1062_optExpr).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv120, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      if (unmatched41) {
        if (_source41.is_CallType) {
          RAST._IExpr _1063_expr = _source41.dtor_obj;
          Dafny.ISequence<RAST._IType> _1064_tpes = _source41.dtor_typeParameters;
          unmatched41 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs47 = (this).LeftParentheses(_1063_expr);
          Dafny.ISequence<Dafny.Rune> _1065_leftP = _let_tmp_rhs47.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1066_rightP = _let_tmp_rhs47.dtor__1;
          if ((_1064_tpes).Equals(Dafny.Sequence<RAST._IType>.FromElements())) {
            return (_1063_expr)._ToString(_pat_let_tv121);
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1065_leftP, (_1063_expr)._ToString(_pat_let_tv122)), _1066_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<")), RAST.__default.SeqToString<RAST._IType>(_1064_tpes, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_1067_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_1068_tpe) => {
              return (_1068_tpe)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1067_ind, RAST.__default.IND));
            })))(_pat_let_tv123), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
        }
      }
      if (unmatched41) {
        if (_source41.is_Call) {
          RAST._IExpr _1069_expr = _source41.dtor_obj;
          Dafny.ISequence<RAST._IExpr> _1070_args = _source41.dtor_arguments;
          unmatched41 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs48 = (this).LeftParentheses(_1069_expr);
          Dafny.ISequence<Dafny.Rune> _1071_leftP = _let_tmp_rhs48.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1072_rightP = _let_tmp_rhs48.dtor__1;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs49 = ((System.Func<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>)(() => {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source46 = (_1069_expr).RightMostIdentifier();
            bool unmatched46 = true;
            if (unmatched46) {
              bool disjunctiveMatch2 = false;
              if (_source46.is_Some) {
                Dafny.ISequence<Dafny.Rune> value4 = _source46.dtor_value;
                if (object.Equals(value4, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))) {
                  disjunctiveMatch2 = true;
                }
              }
              if (_source46.is_Some) {
                Dafny.ISequence<Dafny.Rune> value5 = _source46.dtor_value;
                if (object.Equals(value5, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))) {
                  disjunctiveMatch2 = true;
                }
              }
              if (disjunctiveMatch2) {
                unmatched46 = false;
                return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("["), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
              }
            }
            if (unmatched46) {
              bool disjunctiveMatch3 = false;
              if (_source46.is_Some) {
                Dafny.ISequence<Dafny.Rune> value6 = _source46.dtor_value;
                if (object.Equals(value6, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))) {
                  disjunctiveMatch3 = true;
                }
              }
              if (_source46.is_Some) {
                Dafny.ISequence<Dafny.Rune> value7 = _source46.dtor_value;
                if (object.Equals(value7, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))) {
                  disjunctiveMatch3 = true;
                }
              }
              if (disjunctiveMatch3) {
                unmatched46 = false;
                return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
            }
            if (unmatched46) {
              unmatched46 = false;
              return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            throw new System.Exception("unexpected control point");
          }))();
          Dafny.ISequence<Dafny.Rune> _1073_leftCallP = _let_tmp_rhs49.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1074_rightCallP = _let_tmp_rhs49.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1071_leftP, (_1069_expr)._ToString(_pat_let_tv124)), _1072_rightP), _1073_leftCallP), RAST.__default.SeqToString<RAST._IExpr>(_1070_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_1075_ind) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_1076_arg) => {
            return (_1076_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_1075_ind, RAST.__default.IND));
          })))(_pat_let_tv125), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), _1074_rightCallP);
        }
      }
      if (unmatched41) {
        if (_source41.is_Select) {
          RAST._IExpr _1077_expression = _source41.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _1078_name = _source41.dtor_name;
          unmatched41 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs50 = (this).LeftParentheses(_1077_expression);
          Dafny.ISequence<Dafny.Rune> _1079_leftP = _let_tmp_rhs50.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1080_rightP = _let_tmp_rhs50.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1079_leftP, (_1077_expression)._ToString(_pat_let_tv126)), _1080_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _1078_name);
        }
      }
      if (unmatched41) {
        if (_source41.is_SelectIndex) {
          RAST._IExpr _1081_expression = _source41.dtor_obj;
          RAST._IExpr _1082_range = _source41.dtor_range;
          unmatched41 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs51 = (this).LeftParentheses(_1081_expression);
          Dafny.ISequence<Dafny.Rune> _1083_leftP = _let_tmp_rhs51.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1084_rightP = _let_tmp_rhs51.dtor__1;
          Dafny.ISequence<Dafny.Rune> _1085_rangeStr = (_1082_range)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv127, RAST.__default.IND));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1083_leftP, (_1081_expression)._ToString(_pat_let_tv128)), _1084_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[")), _1085_rangeStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
        }
      }
      if (unmatched41) {
        if (_source41.is_MemberSelect) {
          RAST._IExpr _1086_expression = _source41.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _1087_name = _source41.dtor_name;
          unmatched41 = false;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs52 = (this).LeftParentheses(_1086_expression);
          Dafny.ISequence<Dafny.Rune> _1088_leftP = _let_tmp_rhs52.dtor__0;
          Dafny.ISequence<Dafny.Rune> _1089_rightP = _let_tmp_rhs52.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1088_leftP, (_1086_expression)._ToString(_pat_let_tv129)), _1089_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1087_name);
        }
      }
      if (unmatched41) {
        if (_source41.is_Lambda) {
          Dafny.ISequence<RAST._IFormal> _1090_params = _source41.dtor_params;
          Std.Wrappers._IOption<RAST._IType> _1091_retType = _source41.dtor_retType;
          RAST._IExpr _1092_body = _source41.dtor_body;
          unmatched41 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |"), RAST.__default.SeqToString<RAST._IFormal>(_1090_params, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>>>((_1093_ind) => ((System.Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>)((_1094_arg) => {
            return (_1094_arg)._ToString(_1093_ind);
          })))(_pat_let_tv130), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), (((_1091_retType).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-> "), ((_1091_retType).dtor_value)._ToString(_pat_let_tv131))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), ((((_1091_retType).is_Some) && (!((_1092_body).is_Block))) ? ((RAST.Expr.create_Block(_1092_body))._ToString(_pat_let_tv132)) : ((_1092_body)._ToString(_pat_let_tv133))));
        }
      }
      if (unmatched41) {
        RAST._IExpr _1095_r = _source41;
        unmatched41 = false;
        return RAST.__default.AddIndent((_1095_r).dtor_content, _pat_let_tv134);
      }
      throw new System.Exception("unexpected control point");
    }
    public RAST._IExpr Then(RAST._IExpr rhs2) {
      if ((this).is_StmtExpr) {
        return RAST.Expr.create_StmtExpr((this).dtor_stmt, ((this).dtor_rhs).Then(rhs2));
      } else if (object.Equals(this, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
        return rhs2;
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
    public RAST._IExpr ApplyType(Dafny.ISequence<RAST._IType> typeParameters) {
      if ((new BigInteger((typeParameters).Count)).Sign == 0) {
        return this;
      } else {
        return RAST.Expr.create_CallType(this, typeParameters);
      }
    }
    public RAST._IExpr ApplyType1(RAST._IType typeParameter) {
      return RAST.Expr.create_CallType(this, Dafny.Sequence<RAST._IType>.FromElements(typeParameter));
    }
    public RAST._IExpr Apply(Dafny.ISequence<RAST._IExpr> arguments) {
      return RAST.Expr.create_Call(this, arguments);
    }
    public RAST._IExpr Apply1(RAST._IExpr argument) {
      return RAST.Expr.create_Call(this, Dafny.Sequence<RAST._IExpr>.FromElements(argument));
    }
    public bool IsLhsIdentifier() {
      return ((this).is_Identifier) || (((this).is_Call) && ((((object.Equals((this).dtor_obj, (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("modify!")))) && ((new BigInteger(((this).dtor_arguments).Count)) == (BigInteger.One))) && ((((this).dtor_arguments).Select(BigInteger.Zero)).is_Identifier)) || (((object.Equals((this).dtor_obj, (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("md!")))) && ((new BigInteger(((this).dtor_arguments).Count)) == (BigInteger.One))) && (Dafny.Helpers.Let<RAST._IExpr, bool>(((this).dtor_arguments).Select(BigInteger.Zero), _pat_let8_0 => Dafny.Helpers.Let<RAST._IExpr, bool>(_pat_let8_0, _1096_lhs => (((_1096_lhs).is_Call) && (((_1096_lhs).dtor_obj).is_Select)) && ((((_1096_lhs).dtor_obj).dtor_obj).is_Identifier)))))));
    }
    public Dafny.ISequence<Dafny.Rune> LhsIdentifierName() {
      if ((this).is_Identifier) {
        return (this).dtor_name;
      } else if (object.Equals((this).dtor_obj, (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("modify!")))) {
        return (((this).dtor_arguments).Select(BigInteger.Zero)).dtor_name;
      } else {
        return (((((this).dtor_arguments).Select(BigInteger.Zero)).dtor_obj).dtor_obj).dtor_name;
      }
    }
    public RAST._IExpr Clone() {
      return (RAST.Expr.create_Select(this, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
    }
    public RAST._IPrintingInfo printingInfo { get {
      RAST._IExpr _source47 = this;
      bool unmatched47 = true;
      if (unmatched47) {
        if (_source47.is_RawExpr) {
          unmatched47 = false;
          return RAST.PrintingInfo.create_UnknownPrecedence();
        }
      }
      if (unmatched47) {
        if (_source47.is_ExprFromType) {
          unmatched47 = false;
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      if (unmatched47) {
        if (_source47.is_Identifier) {
          unmatched47 = false;
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      if (unmatched47) {
        if (_source47.is_LiteralInt) {
          unmatched47 = false;
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      if (unmatched47) {
        if (_source47.is_LiteralBool) {
          unmatched47 = false;
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      if (unmatched47) {
        if (_source47.is_LiteralString) {
          unmatched47 = false;
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      if (unmatched47) {
        if (_source47.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> _1097_op = _source47.dtor_op1;
          RAST._IExpr _1098_underlying = _source47.dtor_underlying;
          DAST.Format._IUnaryOpFormat _1099_format = _source47.dtor_format;
          unmatched47 = false;
          Dafny.ISequence<Dafny.Rune> _source48 = _1097_op;
          bool unmatched48 = true;
          if (unmatched48) {
            if (object.Equals(_source48, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) {
              unmatched48 = false;
              return RAST.PrintingInfo.create_SuffixPrecedence(new BigInteger(5));
            }
          }
          if (unmatched48) {
            bool disjunctiveMatch4 = false;
            if (object.Equals(_source48, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) {
              disjunctiveMatch4 = true;
            }
            if (object.Equals(_source48, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) {
              disjunctiveMatch4 = true;
            }
            if (object.Equals(_source48, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"))) {
              disjunctiveMatch4 = true;
            }
            if (object.Equals(_source48, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
              disjunctiveMatch4 = true;
            }
            if (object.Equals(_source48, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"))) {
              disjunctiveMatch4 = true;
            }
            if (disjunctiveMatch4) {
              unmatched48 = false;
              return RAST.PrintingInfo.create_Precedence(new BigInteger(6));
            }
          }
          if (unmatched48) {
            unmatched48 = false;
            return RAST.PrintingInfo.create_UnknownPrecedence();
          }
          throw new System.Exception("unexpected control point");
        }
      }
      if (unmatched47) {
        if (_source47.is_Select) {
          RAST._IExpr _1100_underlying = _source47.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _1101_name = _source47.dtor_name;
          unmatched47 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched47) {
        if (_source47.is_SelectIndex) {
          RAST._IExpr _1102_underlying = _source47.dtor_obj;
          RAST._IExpr _1103_range = _source47.dtor_range;
          unmatched47 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched47) {
        if (_source47.is_MemberSelect) {
          RAST._IExpr _1104_underlying = _source47.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _1105_name = _source47.dtor_name;
          unmatched47 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched47) {
        if (_source47.is_CallType) {
          unmatched47 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched47) {
        if (_source47.is_Call) {
          unmatched47 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched47) {
        if (_source47.is_TypeAscription) {
          RAST._IExpr _1106_left = _source47.dtor_left;
          RAST._IType _1107_tpe = _source47.dtor_tpe;
          unmatched47 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(10), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched47) {
        if (_source47.is_BinaryOp) {
          Dafny.ISequence<Dafny.Rune> _1108_op2 = _source47.dtor_op2;
          RAST._IExpr _1109_left = _source47.dtor_left;
          RAST._IExpr _1110_right = _source47.dtor_right;
          DAST.Format._IBinaryOpFormat _1111_format = _source47.dtor_format2;
          unmatched47 = false;
          Dafny.ISequence<Dafny.Rune> _source49 = _1108_op2;
          bool unmatched49 = true;
          if (unmatched49) {
            bool disjunctiveMatch5 = false;
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) {
              disjunctiveMatch5 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
              disjunctiveMatch5 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
              disjunctiveMatch5 = true;
            }
            if (disjunctiveMatch5) {
              unmatched49 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(20), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched49) {
            bool disjunctiveMatch6 = false;
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) {
              disjunctiveMatch6 = true;
            }
            if (disjunctiveMatch6) {
              unmatched49 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(30), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched49) {
            bool disjunctiveMatch7 = false;
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"))) {
              disjunctiveMatch7 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>"))) {
              disjunctiveMatch7 = true;
            }
            if (disjunctiveMatch7) {
              unmatched49 = false;
              if ((((_1108_op2).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"))) && ((_1109_left).is_TypeAscription)) && (((_1109_left).dtor_tpe).EndsWithNameThatCanAcceptGenerics())) {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(9), RAST.Associativity.create_LeftToRight());
              } else {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(40), RAST.Associativity.create_LeftToRight());
              }
            }
          }
          if (unmatched49) {
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
              unmatched49 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(50), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched49) {
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^"))) {
              unmatched49 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(60), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched49) {
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|"))) {
              unmatched49 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(70), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched49) {
            bool disjunctiveMatch8 = false;
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
              disjunctiveMatch8 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="))) {
              disjunctiveMatch8 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
              disjunctiveMatch8 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))) {
              disjunctiveMatch8 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="))) {
              disjunctiveMatch8 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="))) {
              disjunctiveMatch8 = true;
            }
            if (disjunctiveMatch8) {
              unmatched49 = false;
              if (((((_1108_op2).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) || ((_1108_op2).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<=")))) && ((_1109_left).is_TypeAscription)) && (((_1109_left).dtor_tpe).EndsWithNameThatCanAcceptGenerics())) {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(9), RAST.Associativity.create_LeftToRight());
              } else {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses());
              }
            }
          }
          if (unmatched49) {
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&"))) {
              unmatched49 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(90), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched49) {
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||"))) {
              unmatched49 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(100), RAST.Associativity.create_LeftToRight());
            }
          }
          if (unmatched49) {
            bool disjunctiveMatch9 = false;
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".."))) {
              disjunctiveMatch9 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..="))) {
              disjunctiveMatch9 = true;
            }
            if (disjunctiveMatch9) {
              unmatched49 = false;
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RequiresParentheses());
            }
          }
          if (unmatched49) {
            bool disjunctiveMatch10 = false;
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<="))) {
              disjunctiveMatch10 = true;
            }
            if (object.Equals(_source49, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>="))) {
              disjunctiveMatch10 = true;
            }
            if (disjunctiveMatch10) {
              unmatched49 = false;
              if ((((_1108_op2).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<="))) && ((_1109_left).is_TypeAscription)) && (((_1109_left).dtor_tpe).EndsWithNameThatCanAcceptGenerics())) {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(9), RAST.Associativity.create_LeftToRight());
              } else {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
              }
            }
          }
          if (unmatched49) {
            unmatched49 = false;
            return RAST.PrintingInfo.create_PrecedenceAssociativity(BigInteger.Zero, RAST.Associativity.create_RequiresParentheses());
          }
          throw new System.Exception("unexpected control point");
        }
      }
      if (unmatched47) {
        if (_source47.is_Lambda) {
          unmatched47 = false;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(300), RAST.Associativity.create_LeftToRight());
        }
      }
      if (unmatched47) {
        unmatched47 = false;
        return RAST.PrintingInfo.create_UnknownPrecedence();
      }
      throw new System.Exception("unexpected control point");
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
  public class Expr_ExprFromType : Expr {
    public readonly RAST._IType _tpe;
    public Expr_ExprFromType(RAST._IType tpe) : base() {
      this._tpe = tpe;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_ExprFromType(_tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_ExprFromType;
      return oth != null && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.ExprFromType";
      s += "(";
      s += Dafny.Helpers.ToString(this._tpe);
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
      hash = ((hash << 5) + hash) + 2;
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
      hash = ((hash << 5) + hash) + 3;
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
      hash = ((hash << 5) + hash) + 4;
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
      hash = ((hash << 5) + hash) + 5;
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
    public readonly RAST._IExpr _underlying;
    public readonly Dafny.ISequence<RAST._IAssignIdentifier> _assignments;
    public Expr_StructBuild(RAST._IExpr underlying, Dafny.ISequence<RAST._IAssignIdentifier> assignments) : base() {
      this._underlying = underlying;
      this._assignments = assignments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_StructBuild(_underlying, _assignments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_StructBuild;
      return oth != null && object.Equals(this._underlying, oth._underlying) && object.Equals(this._assignments, oth._assignments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._assignments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.StructBuild";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
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
      hash = ((hash << 5) + hash) + 7;
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
      hash = ((hash << 5) + hash) + 8;
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
      hash = ((hash << 5) + hash) + 9;
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
      hash = ((hash << 5) + hash) + 10;
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
      hash = ((hash << 5) + hash) + 11;
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
  public class Expr_LiteralBool : Expr {
    public readonly bool _bvalue;
    public Expr_LiteralBool(bool bvalue) : base() {
      this._bvalue = bvalue;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_LiteralBool(_bvalue);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_LiteralBool;
      return oth != null && this._bvalue == oth._bvalue;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._bvalue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.LiteralBool";
      s += "(";
      s += Dafny.Helpers.ToString(this._bvalue);
      s += ")";
      return s;
    }
  }
  public class Expr_LiteralString : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _value;
    public readonly bool _binary;
    public readonly bool _verbatim;
    public Expr_LiteralString(Dafny.ISequence<Dafny.Rune> @value, bool binary, bool verbatim) : base() {
      this._value = @value;
      this._binary = binary;
      this._verbatim = verbatim;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_LiteralString(_value, _binary, _verbatim);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_LiteralString;
      return oth != null && object.Equals(this._value, oth._value) && this._binary == oth._binary && this._verbatim == oth._verbatim;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._binary));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._verbatim));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.LiteralString";
      s += "(";
      s += this._value.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._binary);
      s += ", ";
      s += Dafny.Helpers.ToString(this._verbatim);
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
      hash = ((hash << 5) + hash) + 14;
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
  public class Expr_Assign : Expr {
    public readonly Std.Wrappers._IOption<RAST._IAssignLhs> _names;
    public readonly RAST._IExpr _rhs;
    public Expr_Assign(Std.Wrappers._IOption<RAST._IAssignLhs> names, RAST._IExpr rhs) : base() {
      this._names = names;
      this._rhs = rhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Assign(_names, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Assign;
      return oth != null && object.Equals(this._names, oth._names) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._names));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Assign";
      s += "(";
      s += Dafny.Helpers.ToString(this._names);
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
      hash = ((hash << 5) + hash) + 16;
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
      hash = ((hash << 5) + hash) + 17;
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
      hash = ((hash << 5) + hash) + 18;
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
      hash = ((hash << 5) + hash) + 19;
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
      hash = ((hash << 5) + hash) + 20;
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
      hash = ((hash << 5) + hash) + 21;
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
      hash = ((hash << 5) + hash) + 22;
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
  public class Expr_CallType : Expr {
    public readonly RAST._IExpr _obj;
    public readonly Dafny.ISequence<RAST._IType> _typeParameters;
    public Expr_CallType(RAST._IExpr obj, Dafny.ISequence<RAST._IType> typeParameters) : base() {
      this._obj = obj;
      this._typeParameters = typeParameters;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_CallType(_obj, _typeParameters);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_CallType;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._typeParameters, oth._typeParameters);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParameters));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.CallType";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParameters);
      s += ")";
      return s;
    }
  }
  public class Expr_Call : Expr {
    public readonly RAST._IExpr _obj;
    public readonly Dafny.ISequence<RAST._IExpr> _arguments;
    public Expr_Call(RAST._IExpr obj, Dafny.ISequence<RAST._IExpr> arguments) : base() {
      this._obj = obj;
      this._arguments = arguments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Call(_obj, _arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Call;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
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
      hash = ((hash << 5) + hash) + 25;
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
  public class Expr_SelectIndex : Expr {
    public readonly RAST._IExpr _obj;
    public readonly RAST._IExpr _range;
    public Expr_SelectIndex(RAST._IExpr obj, RAST._IExpr range) : base() {
      this._obj = obj;
      this._range = range;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_SelectIndex(_obj, _range);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_SelectIndex;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._range, oth._range);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 26;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._range));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.SelectIndex";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += Dafny.Helpers.ToString(this._range);
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
      hash = ((hash << 5) + hash) + 27;
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
  public class Expr_Lambda : Expr {
    public readonly Dafny.ISequence<RAST._IFormal> _params;
    public readonly Std.Wrappers._IOption<RAST._IType> _retType;
    public readonly RAST._IExpr _body;
    public Expr_Lambda(Dafny.ISequence<RAST._IFormal> @params, Std.Wrappers._IOption<RAST._IType> retType, RAST._IExpr body) : base() {
      this._params = @params;
      this._retType = retType;
      this._body = body;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Lambda(_params, _retType, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Lambda;
      return oth != null && object.Equals(this._params, oth._params) && object.Equals(this._retType, oth._retType) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 28;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._params));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Lambda";
      s += "(";
      s += Dafny.Helpers.ToString(this._params);
      s += ", ";
      s += Dafny.Helpers.ToString(this._retType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }

  public interface _IFn {
    bool is_Fn { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    Dafny.ISequence<RAST._IFormal> dtor_formals { get; }
    Std.Wrappers._IOption<RAST._IType> dtor_returnType { get; }
    Dafny.ISequence<Dafny.Rune> dtor_where { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_body { get; }
    _IFn DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Fn : _IFn {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly Dafny.ISequence<RAST._IFormal> _formals;
    public readonly Std.Wrappers._IOption<RAST._IType> _returnType;
    public readonly Dafny.ISequence<Dafny.Rune> _where;
    public readonly Std.Wrappers._IOption<RAST._IExpr> _body;
    public Fn(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Dafny.ISequence<Dafny.Rune> @where, Std.Wrappers._IOption<RAST._IExpr> body) {
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
    private static readonly RAST._IFn theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParamDecl>.Empty, Dafny.Sequence<RAST._IFormal>.Empty, Std.Wrappers.Option<RAST._IType>.Default(), Dafny.Sequence<Dafny.Rune>.Empty, Std.Wrappers.Option<RAST._IExpr>.Default());
    public static RAST._IFn Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IFn> _TYPE = new Dafny.TypeDescriptor<RAST._IFn>(RAST.Fn.Default());
    public static Dafny.TypeDescriptor<RAST._IFn> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFn create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Dafny.ISequence<Dafny.Rune> @where, Std.Wrappers._IOption<RAST._IExpr> body) {
      return new Fn(name, typeParams, formals, returnType, @where, body);
    }
    public static _IFn create_Fn(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Dafny.ISequence<Dafny.Rune> @where, Std.Wrappers._IOption<RAST._IExpr> body) {
      return create(name, typeParams, formals, returnType, @where, body);
    }
    public bool is_Fn { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
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
      var _pat_let_tv135 = ind;
      var _pat_let_tv136 = ind;
      var _pat_let_tv137 = ind;
      var _pat_let_tv138 = ind;
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn "), (this).dtor_name), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), RAST.__default.SeqToString<RAST._IFormal>((this).dtor_formals, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>>>((_1112_ind) => ((System.Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>)((_1113_formal) => {
        return (_1113_formal)._ToString(_1112_ind);
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
        Std.Wrappers._IOption<RAST._IType> _source50 = (this).dtor_returnType;
        bool unmatched50 = true;
        if (unmatched50) {
          if (_source50.is_Some) {
            RAST._IType _1114_t = _source50.dtor_value;
            unmatched50 = false;
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" -> "), (_1114_t)._ToString(_pat_let_tv135));
          }
        }
        if (unmatched50) {
          unmatched50 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        throw new System.Exception("unexpected control point");
      }))()), ((((this).dtor_where).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), (this).dtor_where)))), ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
        Std.Wrappers._IOption<RAST._IExpr> _source51 = (this).dtor_body;
        bool unmatched51 = true;
        if (unmatched51) {
          if (_source51.is_None) {
            unmatched51 = false;
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";");
          }
        }
        if (unmatched51) {
          RAST._IExpr _1115_body = _source51.dtor_value;
          unmatched51 = false;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"), _pat_let_tv136), RAST.__default.IND), (_1115_body)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv137, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv138), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        throw new System.Exception("unexpected control point");
      }))());
    }
  }
} // end of namespace RAST