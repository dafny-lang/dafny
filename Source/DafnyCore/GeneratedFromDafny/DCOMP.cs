// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

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
            Dafny.ISequence<Dafny.Rune> _in0 = (i).Drop(new BigInteger(2));
            i = _in0;
            goto TAIL_CALL_START;
          }
        } else {
          return true;
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _in1 = (i).Drop(BigInteger.One);
        i = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> idiomatic__rust(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in0 = (i).Drop(new BigInteger(2));
        i = _in0;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in1 = (i).Drop(BigInteger.One);
        i = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in0 = (i).Drop(BigInteger.One);
        i = _in0;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in1 = (i).Drop(BigInteger.One);
        i = _in1;
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
      return ((((new BigInteger((i).Count)).Sign == 1) && (!(DCOMP.__default.has__special(i)))) && (!(DCOMP.__default.reserved__rust).Contains(i))) && (!(DCOMP.__default.reserved__rust__need__prefix).Contains(i));
    }
    public static Dafny.ISequence<Dafny.Rune> escapeName(Dafny.ISequence<Dafny.Rune> n) {
      return DCOMP.__default.escapeIdent((n));
    }
    public static Dafny.ISequence<Dafny.Rune> escapeIdent(Dafny.ISequence<Dafny.Rune> i) {
      if (DCOMP.__default.is__tuple__numeric(i)) {
        return i;
      } else if (DCOMP.__default.is__tuple__builder(i)) {
        return DCOMP.__default.better__tuple__builder__name(i);
      } else if (((i).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) || ((i).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self")))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), i);
      } else if ((DCOMP.__default.reserved__rust).Contains(i)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), i);
      } else if (DCOMP.__default.is__idiomatic__rust__id(i)) {
        return DCOMP.__default.idiomatic__rust(i);
      } else if (DCOMP.__default.is__dafny__generated__id(i)) {
        return i;
      } else {
        Dafny.ISequence<Dafny.Rune> _0_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _0_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeVar(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _0_r = (f);
      if ((DCOMP.__default.reserved__vars).Contains(_0_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _0_r);
      } else {
        return DCOMP.__default.escapeIdent((f));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> AddAssignedPrefix(Dafny.ISequence<Dafny.Rune> rustName) {
      if (((new BigInteger((rustName).Count)) >= (new BigInteger(2))) && (((rustName).Subsequence(BigInteger.Zero, new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.ASSIGNED__PREFIX, (rustName).Drop(new BigInteger(2)));
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.ASSIGNED__PREFIX, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")), rustName);
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethodAux(Dafny.ISequence<DAST._IType> rs, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _0_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source0 = (rs).Select(BigInteger.Zero);
          {
            if (_source0.is_UserDefined) {
              DAST._IResolvedType _1_resolvedType = _source0.dtor_resolved;
              return DCOMP.__default.TraitTypeContainingMethod(_1_resolvedType, dafnyName);
            }
          }
          {
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source1 = _0_res;
        {
          if (_source1.is_Some) {
            return _0_res;
          }
        }
        {
          return DCOMP.__default.TraitTypeContainingMethodAux((rs).Drop(BigInteger.One), dafnyName);
        }
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs0 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_path = _let_tmp_rhs0.dtor_path;
      Dafny.ISequence<DAST._IType> _1_typeArgs = _let_tmp_rhs0.dtor_typeArgs;
      DAST._IResolvedTypeBase _2_kind = _let_tmp_rhs0.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _3_attributes = _let_tmp_rhs0.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4_properMethods = _let_tmp_rhs0.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _5_extendedTypes = _let_tmp_rhs0.dtor_extendedTypes;
      if ((_4_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_5_extendedTypes, dafnyName);
      }
    }
    public static Std.Wrappers._IOption<DCOMP._IExternAttribute> OptExtern(DAST._IAttribute attr, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      if (((attr).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) {
        return Std.Wrappers.Option<DCOMP._IExternAttribute>.create_Some((((new BigInteger(((attr).dtor_args).Count)).Sign == 0) ? (DCOMP.ExternAttribute.create_SimpleExtern(DCOMP.__default.escapeName(dafnyName))) : ((((new BigInteger(((attr).dtor_args).Count)) == (BigInteger.One)) ? (DCOMP.ExternAttribute.create_SimpleExtern(((attr).dtor_args).Select(BigInteger.Zero))) : ((((new BigInteger(((attr).dtor_args).Count)) == (new BigInteger(2))) ? (DCOMP.ExternAttribute.create_AdvancedExtern(DCOMP.__default.ReplaceDotByDoubleColon(((attr).dtor_args).Select(BigInteger.Zero)), ((attr).dtor_args).Select(BigInteger.One))) : (DCOMP.ExternAttribute.create_UnsupportedExtern(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{:extern} supports only 0, 1 or 2 attributes, got "), Std.Strings.__default.OfNat(new BigInteger(((attr).dtor_args).Count)))))))))));
      } else {
        return Std.Wrappers.Option<DCOMP._IExternAttribute>.create_None();
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ReplaceDotByDoubleColon(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, s);
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in0 = (s).Drop(BigInteger.One);
        s = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static DCOMP._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DCOMP._IExternAttribute res = DCOMP.ExternAttribute.Default();
      BigInteger _hi0 = new BigInteger((attributes).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _1_attr;
        _1_attr = DCOMP.__default.OptExtern((attributes).Select(_0_i), dafnyName);
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source0 = _1_attr;
        {
          if (_source0.is_Some) {
            DCOMP._IExternAttribute _2_n = _source0.dtor_value;
            res = _2_n;
            return res;
            goto after_match0;
          }
        }
        {
        }
      after_match0: ;
      }
      res = DCOMP.ExternAttribute.create_NoExtern();
      return res;
    }
    public static DCOMP._IExternAttribute ExtractExternMod(DAST._IModule mod) {
      return DCOMP.__default.ExtractExtern((mod).dtor_attributes, (mod).dtor_name);
    }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("async"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("await"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("const"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("else"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("enum"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ref"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("static"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("struct"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("union"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Keywords"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abstract"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("become"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("box"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("do"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("final"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("macro"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("override"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("priv"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("try"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("typeof"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsized"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("virtual"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("yield"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust__need__prefix { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__vars { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"));
    } }
    public static Dafny.ISequence<Dafny.Rune> ASSIGNED__PREFIX { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_set");
    } }
    public static Dafny.ISequence<Dafny.Rune> IND { get {
      return RAST.__default.IND;
    } }
    public static DAST._IAttribute AttributeOwned { get {
      return DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("owned"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
    } }
  }

  public interface _IOwnership {
    bool is_OwnershipOwned { get; }
    bool is_OwnershipOwnedBox { get; }
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
    public static _IOwnership create_OwnershipOwnedBox() {
      return new Ownership_OwnershipOwnedBox();
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
    public bool is_OwnershipOwnedBox { get { return this is Ownership_OwnershipOwnedBox; } }
    public bool is_OwnershipBorrowed { get { return this is Ownership_OwnershipBorrowed; } }
    public bool is_OwnershipBorrowedMut { get { return this is Ownership_OwnershipBorrowedMut; } }
    public bool is_OwnershipAutoBorrowed { get { return this is Ownership_OwnershipAutoBorrowed; } }
    public static System.Collections.Generic.IEnumerable<_IOwnership> AllSingletonConstructors {
      get {
        yield return Ownership.create_OwnershipOwned();
        yield return Ownership.create_OwnershipOwnedBox();
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
  public class Ownership_OwnershipOwnedBox : Ownership {
    public Ownership_OwnershipOwnedBox() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipOwnedBox();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Ownership_OwnershipOwnedBox;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipOwnedBox";
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
      hash = ((hash << 5) + hash) + 2;
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
      hash = ((hash << 5) + hash) + 3;
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
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipAutoBorrowed";
      return s;
    }
  }

  public interface _IEnvironment {
    bool is_Environment { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_names { get; }
    Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> dtor_types { get; }
    _IEnvironment DowncastClone();
    DCOMP._IEnvironment ToOwned();
    bool CanReadWithoutClone(Dafny.ISequence<Dafny.Rune> name);
    bool HasCloneSemantics(Dafny.ISequence<Dafny.Rune> name);
    Std.Wrappers._IOption<RAST._IType> GetType(Dafny.ISequence<Dafny.Rune> name);
    bool IsBorrowed(Dafny.ISequence<Dafny.Rune> name);
    bool IsBorrowedMut(Dafny.ISequence<Dafny.Rune> name);
    DCOMP._IEnvironment AddAssigned(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe);
    DCOMP._IEnvironment merge(DCOMP._IEnvironment other);
    DCOMP._IEnvironment RemoveAssigned(Dafny.ISequence<Dafny.Rune> name);
  }
  public class Environment : _IEnvironment {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _names;
    public readonly Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _types;
    public Environment(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types) {
      this._names = names;
      this._types = types;
    }
    public _IEnvironment DowncastClone() {
      if (this is _IEnvironment dt) { return dt; }
      return new Environment(_names, _types);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Environment;
      return oth != null && object.Equals(this._names, oth._names) && object.Equals(this._types, oth._types);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._names));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._types));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Environment.Environment";
      s += "(";
      s += Dafny.Helpers.ToString(this._names);
      s += ", ";
      s += Dafny.Helpers.ToString(this._types);
      s += ")";
      return s;
    }
    private static readonly DCOMP._IEnvironment theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Empty);
    public static DCOMP._IEnvironment Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._IEnvironment> _TYPE = new Dafny.TypeDescriptor<DCOMP._IEnvironment>(DCOMP.Environment.Default());
    public static Dafny.TypeDescriptor<DCOMP._IEnvironment> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnvironment create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types) {
      return new Environment(names, types);
    }
    public static _IEnvironment create_Environment(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types) {
      return create(names, types);
    }
    public bool is_Environment { get { return true; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_names {
      get {
        return this._names;
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> dtor_types {
      get {
        return this._types;
      }
    }
    public DCOMP._IEnvironment ToOwned() {
      DCOMP._IEnvironment _0_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_0 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _2_k = (Dafny.ISequence<Dafny.Rune>)_compr_0;
          if (((this).dtor_types).Contains(_2_k)) {
            _coll0.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_2_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_2_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll0);
      }))();
      return DCOMP.Environment.create((_0_dt__update__tmp_h0).dtor_names, _1_dt__update_htypes_h0);
    }
    public static DCOMP._IEnvironment Empty() {
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements());
    }
    public bool CanReadWithoutClone(Dafny.ISequence<Dafny.Rune> name) {
      return (((this).dtor_types).Contains(name)) && ((Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name)).CanReadWithoutClone());
    }
    public bool HasCloneSemantics(Dafny.ISequence<Dafny.Rune> name) {
      return !((this).CanReadWithoutClone(name));
    }
    public Std.Wrappers._IOption<RAST._IType> GetType(Dafny.ISequence<Dafny.Rune> name) {
      if (((this).dtor_types).Contains(name)) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name));
      } else {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public bool IsBorrowed(Dafny.ISequence<Dafny.Rune> name) {
      return (((this).dtor_types).Contains(name)) && ((Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name)).is_Borrowed);
    }
    public bool IsBorrowedMut(Dafny.ISequence<Dafny.Rune> name) {
      return (((this).dtor_types).Contains(name)) && ((Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name)).is_BorrowedMut);
    }
    public DCOMP._IEnvironment AddAssigned(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe)
    {
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_names, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(name)), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update((this).dtor_types, name, tpe));
    }
    public DCOMP._IEnvironment merge(DCOMP._IEnvironment other) {
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_names, (other).dtor_names), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge((this).dtor_types, (other).dtor_types));
    }
    public DCOMP._IEnvironment RemoveAssigned(Dafny.ISequence<Dafny.Rune> name) {
      BigInteger _0_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _0_indexInEnv), ((this).dtor_names).Drop((_0_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
    }
  }

  public interface _IObjectType {
    bool is_RawPointers { get; }
    bool is_RcMut { get; }
    _IObjectType DowncastClone();
  }
  public abstract class ObjectType : _IObjectType {
    public ObjectType() {
    }
    private static readonly DCOMP._IObjectType theDefault = create_RawPointers();
    public static DCOMP._IObjectType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._IObjectType> _TYPE = new Dafny.TypeDescriptor<DCOMP._IObjectType>(DCOMP.ObjectType.Default());
    public static Dafny.TypeDescriptor<DCOMP._IObjectType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IObjectType create_RawPointers() {
      return new ObjectType_RawPointers();
    }
    public static _IObjectType create_RcMut() {
      return new ObjectType_RcMut();
    }
    public bool is_RawPointers { get { return this is ObjectType_RawPointers; } }
    public bool is_RcMut { get { return this is ObjectType_RcMut; } }
    public static System.Collections.Generic.IEnumerable<_IObjectType> AllSingletonConstructors {
      get {
        yield return ObjectType.create_RawPointers();
        yield return ObjectType.create_RcMut();
      }
    }
    public abstract _IObjectType DowncastClone();
  }
  public class ObjectType_RawPointers : ObjectType {
    public ObjectType_RawPointers() : base() {
    }
    public override _IObjectType DowncastClone() {
      if (this is _IObjectType dt) { return dt; }
      return new ObjectType_RawPointers();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.ObjectType_RawPointers;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ObjectType.RawPointers";
      return s;
    }
  }
  public class ObjectType_RcMut : ObjectType {
    public ObjectType_RcMut() : base() {
    }
    public override _IObjectType DowncastClone() {
      if (this is _IObjectType dt) { return dt; }
      return new ObjectType_RcMut();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.ObjectType_RcMut;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ObjectType.RcMut";
      return s;
    }
  }

  public interface _IGenTypeContext {
    bool is_GenTypeContext { get; }
    bool dtor_forTraitParents { get; }
  }
  public class GenTypeContext : _IGenTypeContext {
    public readonly bool _forTraitParents;
    public GenTypeContext(bool forTraitParents) {
      this._forTraitParents = forTraitParents;
    }
    public static bool DowncastClone(bool _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.GenTypeContext;
      return oth != null && this._forTraitParents == oth._forTraitParents;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._forTraitParents));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.GenTypeContext.GenTypeContext";
      s += "(";
      s += Dafny.Helpers.ToString(this._forTraitParents);
      s += ")";
      return s;
    }
    private static readonly bool theDefault = false;
    public static bool Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<bool> _TYPE = new Dafny.TypeDescriptor<bool>(false);
    public static Dafny.TypeDescriptor<bool> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenTypeContext create(bool forTraitParents) {
      return new GenTypeContext(forTraitParents);
    }
    public static _IGenTypeContext create_GenTypeContext(bool forTraitParents) {
      return create(forTraitParents);
    }
    public bool is_GenTypeContext { get { return true; } }
    public bool dtor_forTraitParents {
      get {
        return this._forTraitParents;
      }
    }
    public static bool ForTraitParents() {
      return true;
    }
    public static bool @default() {
      return false;
    }
  }

  public interface _ISelfInfo {
    bool is_NoSelf { get; }
    bool is_ThisTyped { get; }
    Dafny.ISequence<Dafny.Rune> dtor_rSelfName { get; }
    DAST._IType dtor_dafnyType { get; }
    _ISelfInfo DowncastClone();
    bool IsSelf();
  }
  public abstract class SelfInfo : _ISelfInfo {
    public SelfInfo() {
    }
    private static readonly DCOMP._ISelfInfo theDefault = create_NoSelf();
    public static DCOMP._ISelfInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._ISelfInfo> _TYPE = new Dafny.TypeDescriptor<DCOMP._ISelfInfo>(DCOMP.SelfInfo.Default());
    public static Dafny.TypeDescriptor<DCOMP._ISelfInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISelfInfo create_NoSelf() {
      return new SelfInfo_NoSelf();
    }
    public static _ISelfInfo create_ThisTyped(Dafny.ISequence<Dafny.Rune> rSelfName, DAST._IType dafnyType) {
      return new SelfInfo_ThisTyped(rSelfName, dafnyType);
    }
    public bool is_NoSelf { get { return this is SelfInfo_NoSelf; } }
    public bool is_ThisTyped { get { return this is SelfInfo_ThisTyped; } }
    public Dafny.ISequence<Dafny.Rune> dtor_rSelfName {
      get {
        var d = this;
        return ((SelfInfo_ThisTyped)d)._rSelfName;
      }
    }
    public DAST._IType dtor_dafnyType {
      get {
        var d = this;
        return ((SelfInfo_ThisTyped)d)._dafnyType;
      }
    }
    public abstract _ISelfInfo DowncastClone();
    public bool IsSelf() {
      return ((this).is_ThisTyped) && (((this).dtor_rSelfName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")));
    }
  }
  public class SelfInfo_NoSelf : SelfInfo {
    public SelfInfo_NoSelf() : base() {
    }
    public override _ISelfInfo DowncastClone() {
      if (this is _ISelfInfo dt) { return dt; }
      return new SelfInfo_NoSelf();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.SelfInfo_NoSelf;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.SelfInfo.NoSelf";
      return s;
    }
  }
  public class SelfInfo_ThisTyped : SelfInfo {
    public readonly Dafny.ISequence<Dafny.Rune> _rSelfName;
    public readonly DAST._IType _dafnyType;
    public SelfInfo_ThisTyped(Dafny.ISequence<Dafny.Rune> rSelfName, DAST._IType dafnyType) : base() {
      this._rSelfName = rSelfName;
      this._dafnyType = dafnyType;
    }
    public override _ISelfInfo DowncastClone() {
      if (this is _ISelfInfo dt) { return dt; }
      return new SelfInfo_ThisTyped(_rSelfName, _dafnyType);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.SelfInfo_ThisTyped;
      return oth != null && object.Equals(this._rSelfName, oth._rSelfName) && object.Equals(this._dafnyType, oth._dafnyType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rSelfName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dafnyType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.SelfInfo.ThisTyped";
      s += "(";
      s += this._rSelfName.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._dafnyType);
      s += ")";
      return s;
    }
  }

  public interface _IExternAttribute {
    bool is_NoExtern { get; }
    bool is_SimpleExtern { get; }
    bool is_AdvancedExtern { get; }
    bool is_UnsupportedExtern { get; }
    Dafny.ISequence<Dafny.Rune> dtor_overrideName { get; }
    Dafny.ISequence<Dafny.Rune> dtor_enclosingModule { get; }
    Dafny.ISequence<Dafny.Rune> dtor_reason { get; }
    _IExternAttribute DowncastClone();
  }
  public abstract class ExternAttribute : _IExternAttribute {
    public ExternAttribute() {
    }
    private static readonly DCOMP._IExternAttribute theDefault = create_NoExtern();
    public static DCOMP._IExternAttribute Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._IExternAttribute> _TYPE = new Dafny.TypeDescriptor<DCOMP._IExternAttribute>(DCOMP.ExternAttribute.Default());
    public static Dafny.TypeDescriptor<DCOMP._IExternAttribute> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExternAttribute create_NoExtern() {
      return new ExternAttribute_NoExtern();
    }
    public static _IExternAttribute create_SimpleExtern(Dafny.ISequence<Dafny.Rune> overrideName) {
      return new ExternAttribute_SimpleExtern(overrideName);
    }
    public static _IExternAttribute create_AdvancedExtern(Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<Dafny.Rune> overrideName) {
      return new ExternAttribute_AdvancedExtern(enclosingModule, overrideName);
    }
    public static _IExternAttribute create_UnsupportedExtern(Dafny.ISequence<Dafny.Rune> reason) {
      return new ExternAttribute_UnsupportedExtern(reason);
    }
    public bool is_NoExtern { get { return this is ExternAttribute_NoExtern; } }
    public bool is_SimpleExtern { get { return this is ExternAttribute_SimpleExtern; } }
    public bool is_AdvancedExtern { get { return this is ExternAttribute_AdvancedExtern; } }
    public bool is_UnsupportedExtern { get { return this is ExternAttribute_UnsupportedExtern; } }
    public Dafny.ISequence<Dafny.Rune> dtor_overrideName {
      get {
        var d = this;
        if (d is ExternAttribute_SimpleExtern) { return ((ExternAttribute_SimpleExtern)d)._overrideName; }
        return ((ExternAttribute_AdvancedExtern)d)._overrideName;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_enclosingModule {
      get {
        var d = this;
        return ((ExternAttribute_AdvancedExtern)d)._enclosingModule;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_reason {
      get {
        var d = this;
        return ((ExternAttribute_UnsupportedExtern)d)._reason;
      }
    }
    public abstract _IExternAttribute DowncastClone();
  }
  public class ExternAttribute_NoExtern : ExternAttribute {
    public ExternAttribute_NoExtern() : base() {
    }
    public override _IExternAttribute DowncastClone() {
      if (this is _IExternAttribute dt) { return dt; }
      return new ExternAttribute_NoExtern();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.ExternAttribute_NoExtern;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ExternAttribute.NoExtern";
      return s;
    }
  }
  public class ExternAttribute_SimpleExtern : ExternAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _overrideName;
    public ExternAttribute_SimpleExtern(Dafny.ISequence<Dafny.Rune> overrideName) : base() {
      this._overrideName = overrideName;
    }
    public override _IExternAttribute DowncastClone() {
      if (this is _IExternAttribute dt) { return dt; }
      return new ExternAttribute_SimpleExtern(_overrideName);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.ExternAttribute_SimpleExtern;
      return oth != null && object.Equals(this._overrideName, oth._overrideName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overrideName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ExternAttribute.SimpleExtern";
      s += "(";
      s += this._overrideName.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ExternAttribute_AdvancedExtern : ExternAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _enclosingModule;
    public readonly Dafny.ISequence<Dafny.Rune> _overrideName;
    public ExternAttribute_AdvancedExtern(Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<Dafny.Rune> overrideName) : base() {
      this._enclosingModule = enclosingModule;
      this._overrideName = overrideName;
    }
    public override _IExternAttribute DowncastClone() {
      if (this is _IExternAttribute dt) { return dt; }
      return new ExternAttribute_AdvancedExtern(_enclosingModule, _overrideName);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.ExternAttribute_AdvancedExtern;
      return oth != null && object.Equals(this._enclosingModule, oth._enclosingModule) && object.Equals(this._overrideName, oth._overrideName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._enclosingModule));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overrideName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ExternAttribute.AdvancedExtern";
      s += "(";
      s += this._enclosingModule.ToVerbatimString(true);
      s += ", ";
      s += this._overrideName.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ExternAttribute_UnsupportedExtern : ExternAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _reason;
    public ExternAttribute_UnsupportedExtern(Dafny.ISequence<Dafny.Rune> reason) : base() {
      this._reason = reason;
    }
    public override _IExternAttribute DowncastClone() {
      if (this is _IExternAttribute dt) { return dt; }
      return new ExternAttribute_UnsupportedExtern(_reason);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.ExternAttribute_UnsupportedExtern;
      return oth != null && object.Equals(this._reason, oth._reason);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._reason));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ExternAttribute.UnsupportedExtern";
      s += "(";
      s += this._reason.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public partial class COMP {
    public COMP() {
      this.error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.Default();
      this.optimizations = Dafny.Sequence<Func<RAST._IMod, RAST._IMod>>.Empty;
      this._UnicodeChars = false;
      this._ObjectType = DCOMP.ObjectType.Default();
    }
    public RAST._IType Object(RAST._IType underlying) {
      if (((this).ObjectType).is_RawPointers) {
        return RAST.__default.PtrType(underlying);
      } else {
        return RAST.__default.ObjectType(underlying);
      }
    }
    public RAST._IExpr UnreachablePanicIfVerified(Dafny.ISequence<Dafny.Rune> optText) {
      if (((this).ObjectType).is_RawPointers) {
        return RAST.__default.Unsafe(RAST.Expr.create_Block(((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hint"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unreachable_unchecked"))).Apply0()));
      } else if ((optText).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply0();
      } else {
        return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(optText, false, false));
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> error {get; set;}
    public Dafny.ISequence<Func<RAST._IMod, RAST._IMod>> optimizations {get; set;}
    public void __ctor(bool unicodeChars, DCOMP._IObjectType objectType)
    {
      (this)._UnicodeChars = unicodeChars;
      (this)._ObjectType = objectType;
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      (this).optimizations = Dafny.Sequence<Func<RAST._IMod, RAST._IMod>>.FromElements(FactorPathsOptimization.__default.apply);
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ContainingPathToRust(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      return Std.Collections.Seq.__default.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_0_i) => {
        return DCOMP.__default.escapeName((_0_i));
      })), containingPath);
    }
    public DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> s = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default();
      _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs0 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName((mod).dtor_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_innerPath = _let_tmp_rhs0.dtor__0;
      Dafny.ISequence<Dafny.Rune> _1_innerName = _let_tmp_rhs0.dtor__1;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2_containingPath;
      _2_containingPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, _0_innerPath);
      Dafny.ISequence<Dafny.Rune> _3_modName;
      _3_modName = DCOMP.__default.escapeName(_1_innerName);
      if (((mod).dtor_body).is_None) {
        s = DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_2_containingPath), RAST.Mod.create_ExternMod(_3_modName));
      } else {
        DCOMP._IExternAttribute _4_optExtern;
        _4_optExtern = DCOMP.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IModDecl> _5_body;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _6_allmodules;
        Dafny.ISequence<RAST._IModDecl> _out0;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out1;
        (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2_containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1_innerName)), out _out0, out _out1);
        _5_body = _out0;
        _6_allmodules = _out1;
        if ((_4_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _5_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.__default.crate).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_4_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _5_body);
          }
        } else if ((_4_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_4_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_4_optExtern).dtor_reason);
        }
        s = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_2_containingPath), RAST.Mod.create_Mod(_3_modName, _5_body)), _6_allmodules);
      }
      return s;
    }
    public void GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath, out Dafny.ISequence<RAST._IModDecl> s, out DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> allmodules)
    {
      s = Dafny.Sequence<RAST._IModDecl>.Empty;
      allmodules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default();
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      allmodules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi0 = new BigInteger((body).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        Dafny.ISequence<RAST._IModDecl> _1_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source0 = (body).Select(_0_i);
        {
          if (_source0.is_Module) {
            DAST._IModule _2_m = _source0.dtor_Module_a0;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _3_mm;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out0;
            _out0 = (this).GenModule(_2_m, containingPath);
            _3_mm = _out0;
            allmodules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(allmodules, _3_mm);
            _1_generated = Dafny.Sequence<RAST._IModDecl>.FromElements();
            goto after_match0;
          }
        }
        {
          if (_source0.is_Class) {
            DAST._IClass _4_c = _source0.dtor_Class_a0;
            Dafny.ISequence<RAST._IModDecl> _out1;
            _out1 = (this).GenClass(_4_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_4_c).dtor_name)));
            _1_generated = _out1;
            goto after_match0;
          }
        }
        {
          if (_source0.is_Trait) {
            DAST._ITrait _5_t = _source0.dtor_Trait_a0;
            Dafny.ISequence<RAST._IModDecl> _out2;
            _out2 = (this).GenTrait(_5_t, containingPath);
            _1_generated = _out2;
            goto after_match0;
          }
        }
        {
          if (_source0.is_Newtype) {
            DAST._INewtype _6_n = _source0.dtor_Newtype_a0;
            Dafny.ISequence<RAST._IModDecl> _out3;
            _out3 = (this).GenNewtype(_6_n);
            _1_generated = _out3;
            goto after_match0;
          }
        }
        {
          if (_source0.is_SynonymType) {
            DAST._ISynonymType _7_s = _source0.dtor_SynonymType_a0;
            Dafny.ISequence<RAST._IModDecl> _out4;
            _out4 = (this).GenSynonymType(_7_s);
            _1_generated = _out4;
            goto after_match0;
          }
        }
        {
          DAST._IDatatype _8_d = _source0.dtor_Datatype_a0;
          Dafny.ISequence<RAST._IModDecl> _out5;
          _out5 = (this).GenDatatype(_8_d);
          _1_generated = _out5;
        }
      after_match0: ;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1_generated);
      }
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _0_genTpConstraint;
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) {
        _0_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq);
      } else {
        _0_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType);
      }
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _0_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_0_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _0_genTpConstraint);
    }
    public void GenTypeParameters(Dafny.ISequence<DAST._ITypeArgDecl> @params, out Dafny.ISequence<DAST._IType> typeParamsSeq, out Dafny.ISequence<RAST._IType> typeParams, out Dafny.ISequence<RAST._ITypeParamDecl> constrainedTypeParams, out Dafny.ISequence<Dafny.Rune> whereConstraints)
    {
      typeParamsSeq = Dafny.Sequence<DAST._IType>.Empty;
      typeParams = Dafny.Sequence<RAST._IType>.Empty;
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Empty;
      whereConstraints = Dafny.Sequence<Dafny.Rune>.Empty;
      typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      whereConstraints = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger((@params).Count)).Sign == 1) {
        BigInteger _hi0 = new BigInteger((@params).Count);
        for (BigInteger _0_tpI = BigInteger.Zero; _0_tpI < _hi0; _0_tpI++) {
          DAST._ITypeArgDecl _1_tp;
          _1_tp = (@params).Select(_0_tpI);
          DAST._IType _2_typeArg;
          RAST._ITypeParamDecl _3_typeParam;
          DAST._IType _out0;
          RAST._ITypeParamDecl _out1;
          (this).GenTypeParam(_1_tp, out _out0, out _out1);
          _2_typeArg = _out0;
          _3_typeParam = _out1;
          RAST._IType _4_rType;
          RAST._IType _out2;
          _out2 = (this).GenType(_2_typeArg, DCOMP.GenTypeContext.@default());
          _4_rType = _out2;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_2_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_4_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_3_typeParam));
        }
      }
    }
    public bool IsSameResolvedTypeAnyArgs(DAST._IResolvedType r1, DAST._IResolvedType r2)
    {
      return (((r1).dtor_path).Equals((r2).dtor_path)) && (object.Equals((r1).dtor_kind, (r2).dtor_kind));
    }
    public bool IsSameResolvedType(DAST._IResolvedType r1, DAST._IResolvedType r2)
    {
      return ((this).IsSameResolvedTypeAnyArgs(r1, r2)) && (((r1).dtor_typeArgs).Equals((r2).dtor_typeArgs));
    }
    public Dafny.ISet<Dafny.ISequence<Dafny.Rune>> GatherTypeParamNames(Dafny.ISet<Dafny.ISequence<Dafny.Rune>> types, RAST._IType typ)
    {
      return (typ).Fold<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>(types, ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>, RAST._IType, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)((_0_types, _1_currentType) => {
        return (((_1_currentType).is_TIdentifier) ? (Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_0_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1_currentType).dtor_name))) : (_0_types));
      })));
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _3_whereConstraints;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      Dafny.ISequence<Dafny.Rune> _out3;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2, out _out3);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      _3_whereConstraints = _out3;
      Dafny.ISequence<Dafny.Rune> _4_constrainedTypeParams;
      _4_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _5_fields;
      _5_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _6_fieldInits;
      _6_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _7_usedTypeParams;
      _7_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi0 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _8_fieldI = BigInteger.Zero; _8_fieldI < _hi0; _8_fieldI++) {
        DAST._IField _9_field;
        _9_field = ((c).dtor_fields).Select(_8_fieldI);
        RAST._IType _10_fieldType;
        RAST._IType _out4;
        _out4 = (this).GenType(((_9_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _10_fieldType = _out4;
        _7_usedTypeParams = (this).GatherTypeParamNames(_7_usedTypeParams, _10_fieldType);
        Dafny.ISequence<Dafny.Rune> _11_fieldRustName;
        _11_fieldRustName = DCOMP.__default.escapeVar(((_9_field).dtor_formal).dtor_name);
        _5_fields = Dafny.Sequence<RAST._IField>.Concat(_5_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_11_fieldRustName, _10_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source0 = (_9_field).dtor_defaultValue;
        {
          if (_source0.is_Some) {
            DAST._IExpression _12_e = _source0.dtor_value;
            {
              RAST._IExpr _13_expr;
              DCOMP._IOwnership _14___v51;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _15___v52;
              RAST._IExpr _out5;
              DCOMP._IOwnership _out6;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
              (this).GenExpr(_12_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out5, out _out6, out _out7);
              _13_expr = _out5;
              _14___v51 = _out6;
              _15___v52 = _out7;
              _6_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_6_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_11_fieldRustName, _13_expr)));
            }
            goto after_match0;
          }
        }
        {
          {
            RAST._IExpr _16_default;
            _16_default = RAST.__default.std__default__Default__default;
            if ((_10_fieldType).IsObjectOrPointer()) {
              _16_default = (_10_fieldType).ToNullExpr();
            }
            _6_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_6_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_11_fieldRustName, _16_default)));
          }
        }
      after_match0: ;
      }
      BigInteger _hi1 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _17_typeParamI = BigInteger.Zero; _17_typeParamI < _hi1; _17_typeParamI++) {
        DAST._IType _18_typeArg;
        RAST._ITypeParamDecl _19_typeParam;
        DAST._IType _out8;
        RAST._ITypeParamDecl _out9;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_17_typeParamI), out _out8, out _out9);
        _18_typeArg = _out8;
        _19_typeParam = _out9;
        RAST._IType _20_rTypeArg;
        RAST._IType _out10;
        _out10 = (this).GenType(_18_typeArg, DCOMP.GenTypeContext.@default());
        _20_rTypeArg = _out10;
        if ((_7_usedTypeParams).Contains((_19_typeParam).dtor_name)) {
          goto continue_0;
        }
        _5_fields = Dafny.Sequence<RAST._IField>.Concat(_5_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_17_typeParamI)), RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_20_rTypeArg))))));
        _6_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_6_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_17_typeParamI)), (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsExpr())));
      continue_0: ;
      }
    after_0: ;
      DCOMP._IExternAttribute _21_extern;
      _21_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _22_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_21_extern).is_SimpleExtern) {
        _22_className = (_21_extern).dtor_overrideName;
      } else {
        _22_className = DCOMP.__default.escapeName((c).dtor_name);
        if ((_21_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _23_struct;
      _23_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _22_className, _2_rTypeParamsDecls, RAST.Fields.create_NamedFields(_5_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_21_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_23_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _24_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _25_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out11;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out12;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _0_typeParamsSeq, out _out11, out _out12);
      _24_implBody = _out11;
      _25_traitBodies = _out12;
      if (((_21_extern).is_NoExtern) && (!(_22_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _24_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.__default.SelfOwned)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel((this).allocate)).AsExpr()).ApplyType1(RAST.__default.SelfOwned)).Apply0())))), _24_implBody);
      }
      RAST._IType _26_selfTypeForImpl = RAST.Type.Default();
      if (((_21_extern).is_NoExtern) || ((_21_extern).is_UnsupportedExtern)) {
        _26_selfTypeForImpl = RAST.Type.create_TIdentifier(_22_className);
      } else if ((_21_extern).is_AdvancedExtern) {
        _26_selfTypeForImpl = (((RAST.__default.crate).MSel((_21_extern).dtor_enclosingModule)).MSel((_21_extern).dtor_overrideName)).AsType();
      } else if ((_21_extern).is_SimpleExtern) {
        _26_selfTypeForImpl = RAST.Type.create_TIdentifier((_21_extern).dtor_overrideName);
      }
      if ((new BigInteger((_24_implBody).Count)).Sign == 1) {
        RAST._IImpl _27_i;
        _27_i = RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(_26_selfTypeForImpl, _1_rTypeParams), _3_whereConstraints, _24_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_27_i)));
      }
      RAST._IType _28_genSelfPath;
      RAST._IType _out13;
      _out13 = DCOMP.COMP.GenPathType(path);
      _28_genSelfPath = _out13;
      if (!(_22_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(RAST.__default.AnyTrait))), RAST.Type.create_TypeApp(_28_genSelfPath, _1_rTypeParams), _3_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(RAST.__default.AnyTrait)))))))));
      }
      Dafny.ISequence<DAST._IType> _29_superClasses;
      if ((_22_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        _29_superClasses = Dafny.Sequence<DAST._IType>.FromElements();
      } else {
        _29_superClasses = (c).dtor_superClasses;
      }
      BigInteger _hi2 = new BigInteger((_29_superClasses).Count);
      for (BigInteger _30_i = BigInteger.Zero; _30_i < _hi2; _30_i++) {
        DAST._IType _31_superClass;
        _31_superClass = (_29_superClasses).Select(_30_i);
        DAST._IType _source1 = _31_superClass;
        {
          if (_source1.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source1.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _32_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _33_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _34_properMethods = resolved0.dtor_properMethods;
              {
                RAST._IType _35_pathStr;
                RAST._IType _out14;
                _out14 = DCOMP.COMP.GenPathType(_32_traitPath);
                _35_pathStr = _out14;
                Dafny.ISequence<RAST._IType> _36_typeArgs;
                Dafny.ISequence<RAST._IType> _out15;
                _out15 = (this).GenTypeArgs(_33_typeArgs, DCOMP.GenTypeContext.@default());
                _36_typeArgs = _out15;
                Dafny.ISequence<RAST._IImplMember> _37_body;
                _37_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_25_traitBodies).Contains(_32_traitPath)) {
                  _37_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_25_traitBodies,_32_traitPath);
                }
                RAST._IType _38_traitType;
                _38_traitType = RAST.Type.create_TypeApp(_35_pathStr, _36_typeArgs);
                if (!((_21_extern).is_NoExtern)) {
                  if (((new BigInteger((_37_body).Count)).Sign == 0) && ((new BigInteger((_34_properMethods).Count)).Sign != 0)) {
                    goto continue_1;
                  }
                  if ((new BigInteger((_37_body).Count)) != (new BigInteger((_34_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_39_s) => {
  return ((_39_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_38_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_34_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_40_s) => {
  return (_40_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _41_x;
                _41_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, _38_traitType, RAST.Type.create_TypeApp(_28_genSelfPath, _1_rTypeParams), _3_whereConstraints, _37_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_41_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_38_traitType))), RAST.Type.create_TypeApp(_28_genSelfPath, _1_rTypeParams), _3_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_38_traitType)))))))));
              }
              goto after_match1;
            }
          }
        }
        {
        }
      after_match1: ;
      continue_1: ;
      }
    after_1: ;
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      _0_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1_typeParamDecls;
      _1_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _2_typeParams;
      _2_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi0 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _3_tpI = BigInteger.Zero; _3_tpI < _hi0; _3_tpI++) {
          DAST._ITypeArgDecl _4_tp;
          _4_tp = ((t).dtor_typeParams).Select(_3_tpI);
          DAST._IType _5_typeArg;
          RAST._ITypeParamDecl _6_typeParamDecl;
          DAST._IType _out0;
          RAST._ITypeParamDecl _out1;
          (this).GenTypeParam(_4_tp, out _out0, out _out1);
          _5_typeArg = _out0;
          _6_typeParamDecl = _out1;
          _0_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_0_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_5_typeArg));
          _1_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_6_typeParamDecl));
          RAST._IType _7_typeParam;
          RAST._IType _out2;
          _out2 = (this).GenType(_5_typeArg, DCOMP.GenTypeContext.@default());
          _7_typeParam = _out2;
          _2_typeParams = Dafny.Sequence<RAST._IType>.Concat(_2_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_7_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _8_fullPath;
      _8_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _9_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _10___v56;
      Dafny.ISequence<RAST._IImplMember> _out3;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out4;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_8_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _0_typeParamsSeq, out _out3, out _out4);
      _9_implBody = _out3;
      _10___v56 = _out4;
      Dafny.ISequence<RAST._IType> _11_parents;
      _11_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi1 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _12_i = BigInteger.Zero; _12_i < _hi1; _12_i++) {
        RAST._IType _13_tpe;
        RAST._IType _out5;
        _out5 = (this).GenType(((t).dtor_parents).Select(_12_i), DCOMP.GenTypeContext.ForTraitParents());
        _13_tpe = _out5;
        _11_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_11_parents, Dafny.Sequence<RAST._IType>.FromElements(_13_tpe)), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply1(RAST.Type.create_DynType(_13_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _2_typeParams), _11_parents, _9_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _3_whereConstraints;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      Dafny.ISequence<Dafny.Rune> _out3;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2, out _out3);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      _3_whereConstraints = _out3;
      Dafny.ISequence<Dafny.Rune> _4_constrainedTypeParams;
      _4_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _5_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source0 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      {
        if (_source0.is_Some) {
          RAST._IType _6_v = _source0.dtor_value;
          _5_underlyingType = _6_v;
          goto after_match0;
        }
      }
      {
        RAST._IType _out4;
        _out4 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _5_underlyingType = _out4;
      }
    after_match0: ;
      DAST._IType _7_resultingType;
      _7_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _8_newtypeName;
      _8_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _8_newtypeName, _2_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _5_underlyingType))))));
      RAST._IExpr _9_fnBody;
      _9_fnBody = RAST.Expr.create_Identifier(_8_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source1 = (c).dtor_witnessExpr;
      {
        if (_source1.is_Some) {
          DAST._IExpression _10_e = _source1.dtor_value;
          {
            DAST._IExpression _11_e;
            if (object.Equals((c).dtor_base, _7_resultingType)) {
              _11_e = _10_e;
            } else {
              _11_e = DAST.Expression.create_Convert(_10_e, (c).dtor_base, _7_resultingType);
            }
            RAST._IExpr _12_eStr;
            DCOMP._IOwnership _13___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14___v58;
            RAST._IExpr _out5;
            DCOMP._IOwnership _out6;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
            (this).GenExpr(_11_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out5, out _out6, out _out7);
            _12_eStr = _out5;
            _13___v57 = _out6;
            _14___v58 = _out7;
            _9_fnBody = (_9_fnBody).Apply1(_12_eStr);
          }
          goto after_match1;
        }
      }
      {
        {
          _9_fnBody = (_9_fnBody).Apply1(RAST.__default.std__default__Default__default);
        }
      }
    after_match1: ;
      RAST._IImplMember _15_body;
      _15_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_9_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source2 = (c).dtor_constraint;
      {
        if (_source2.is_None) {
          goto after_match2;
        }
      }
      {
        DAST._INewtypeConstraint value0 = _source2.dtor_value;
        DAST._IFormal _16_formal = value0.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _17_constraintStmts = value0.dtor_constraintStmts;
        RAST._IExpr _18_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _19___v59;
        DCOMP._IEnvironment _20_newEnv;
        RAST._IExpr _out8;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out9;
        DCOMP._IEnvironment _out10;
        (this).GenStmts(_17_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out8, out _out9, out _out10);
        _18_rStmts = _out8;
        _19___v59 = _out9;
        _20_newEnv = _out10;
        Dafny.ISequence<RAST._IFormal> _21_rFormals;
        Dafny.ISequence<RAST._IFormal> _out11;
        _out11 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_16_formal), false);
        _21_rFormals = _out11;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_8_newtypeName), _1_rTypeParams), _3_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _21_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_18_rStmts))))))));
      }
    after_match2: ;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_8_newtypeName), _1_rTypeParams), _3_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_15_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_8_newtypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.Borrow((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"))))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_8_newtypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_5_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(((RAST.Path.create_Self()).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))).AsType())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.Borrow((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _3_whereConstraints;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      Dafny.ISequence<Dafny.Rune> _out3;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2, out _out3);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      _3_whereConstraints = _out3;
      Dafny.ISequence<Dafny.Rune> _4_synonymTypeName;
      _4_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _5_resultingType;
      RAST._IType _out4;
      _out4 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _5_resultingType = _out4;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _4_synonymTypeName, _2_rTypeParamsDecls, _5_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _6_defaultConstrainedTypeParams;
      _6_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source0 = (c).dtor_witnessExpr;
      {
        if (_source0.is_Some) {
          DAST._IExpression _7_e = _source0.dtor_value;
          {
            RAST._IExpr _8_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _9___v60;
            DCOMP._IEnvironment _10_newEnv;
            RAST._IExpr _out5;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out6;
            DCOMP._IEnvironment _out7;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out5, out _out6, out _out7);
            _8_rStmts = _out5;
            _9___v60 = _out6;
            _10_newEnv = _out7;
            RAST._IExpr _11_rExpr;
            DCOMP._IOwnership _12___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _13___v62;
            RAST._IExpr _out8;
            DCOMP._IOwnership _out9;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out10;
            (this).GenExpr(_7_e, DCOMP.SelfInfo.create_NoSelf(), _10_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out8, out _out9, out _out10);
            _11_rExpr = _out8;
            _12___v61 = _out9;
            _13___v62 = _out10;
            Dafny.ISequence<Dafny.Rune> _14_constantName;
            _14_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_14_constantName, _6_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_5_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_8_rStmts).Then(_11_rExpr)))))));
          }
          goto after_match0;
        }
      }
      {
      }
    after_match0: ;
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source0 = t;
      {
        if (_source0.is_UserDefined) {
          return true;
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<DAST._IType> _0_ts = _source0.dtor_Tuple_a0;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1_ts).UniqueElements, true, (((_forall_var_0) => {
            DAST._IType _2_t = (DAST._IType)_forall_var_0;
            return !((_1_ts).Contains(_2_t)) || ((this).TypeIsEq(_2_t));
          }))))(_0_ts);
        }
      }
      {
        if (_source0.is_Array) {
          DAST._IType _3_t = _source0.dtor_element;
          return (this).TypeIsEq(_3_t);
        }
      }
      {
        if (_source0.is_Seq) {
          DAST._IType _4_t = _source0.dtor_element;
          return (this).TypeIsEq(_4_t);
        }
      }
      {
        if (_source0.is_Set) {
          DAST._IType _5_t = _source0.dtor_element;
          return (this).TypeIsEq(_5_t);
        }
      }
      {
        if (_source0.is_Multiset) {
          DAST._IType _6_t = _source0.dtor_element;
          return (this).TypeIsEq(_6_t);
        }
      }
      {
        if (_source0.is_Map) {
          DAST._IType _7_k = _source0.dtor_key;
          DAST._IType _8_v = _source0.dtor_value;
          return ((this).TypeIsEq(_7_k)) && ((this).TypeIsEq(_8_v));
        }
      }
      {
        if (_source0.is_SetBuilder) {
          DAST._IType _9_t = _source0.dtor_element;
          return (this).TypeIsEq(_9_t);
        }
      }
      {
        if (_source0.is_MapBuilder) {
          DAST._IType _10_k = _source0.dtor_key;
          DAST._IType _11_v = _source0.dtor_value;
          return ((this).TypeIsEq(_10_k)) && ((this).TypeIsEq(_11_v));
        }
      }
      {
        if (_source0.is_Arrow) {
          return false;
        }
      }
      {
        if (_source0.is_Primitive) {
          return true;
        }
      }
      {
        if (_source0.is_Passthrough) {
          return true;
        }
      }
      {
        if (_source0.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _12_i = _source0.dtor_TypeArg_a0;
          return true;
        }
      }
      {
        return true;
      }
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_0_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_0_c).dtor_ctors).UniqueElements, true, (((_forall_var_0) => {
        DAST._IDatatypeCtor _1_ctor = (DAST._IDatatypeCtor)_forall_var_0;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1_ctor).dtor_args).UniqueElements, true, (((_forall_var_1) => {
          DAST._IDatatypeDtor _2_arg = (DAST._IDatatypeDtor)_forall_var_1;
          return !((((_0_c).dtor_ctors).Contains(_1_ctor)) && (((_1_ctor).dtor_args).Contains(_2_arg))) || ((this).TypeIsEq(((_2_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public RAST._IExpr write(RAST._IExpr r, bool final)
    {
      RAST._IExpr _0_result = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter")), r));
      if (final) {
        return _0_result;
      } else {
        return RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"), _0_result, DAST.Format.UnaryOpFormat.create_NoFormat());
      }
    }
    public RAST._IExpr writeStr(Dafny.ISequence<Dafny.Rune> s, bool final)
    {
      return (this).write(RAST.Expr.create_LiteralString(s, false, false), false);
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _3_whereConstraints;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      Dafny.ISequence<Dafny.Rune> _out3;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2, out _out3);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      _3_whereConstraints = _out3;
      Dafny.ISequence<Dafny.Rune> _4_datatypeName;
      _4_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _5_ctors;
      _5_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _6_variances;
      _6_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_7_typeParamDecl) => {
        return (_7_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      Dafny.ISequence<RAST._IExpr> _8_singletonConstructors;
      _8_singletonConstructors = Dafny.Sequence<RAST._IExpr>.FromElements();
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _9_usedTypeParams;
      _9_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi0 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _10_i = BigInteger.Zero; _10_i < _hi0; _10_i++) {
        DAST._IDatatypeCtor _11_ctor;
        _11_ctor = ((c).dtor_ctors).Select(_10_i);
        Dafny.ISequence<RAST._IField> _12_ctorArgs;
        _12_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _13_isNumeric;
        _13_isNumeric = false;
        if ((new BigInteger(((_11_ctor).dtor_args).Count)).Sign == 0) {
          RAST._IExpr _14_instantiation;
          _14_instantiation = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_4_datatypeName)).FSel(DCOMP.__default.escapeName((_11_ctor).dtor_name)), Dafny.Sequence<RAST._IAssignIdentifier>.FromElements());
          if ((this).IsRcWrapped((c).dtor_attributes)) {
            _14_instantiation = RAST.__default.RcNew(_14_instantiation);
          }
          _8_singletonConstructors = Dafny.Sequence<RAST._IExpr>.Concat(_8_singletonConstructors, Dafny.Sequence<RAST._IExpr>.FromElements(_14_instantiation));
        }
        BigInteger _hi1 = new BigInteger(((_11_ctor).dtor_args).Count);
        for (BigInteger _15_j = BigInteger.Zero; _15_j < _hi1; _15_j++) {
          DAST._IDatatypeDtor _16_dtor;
          _16_dtor = ((_11_ctor).dtor_args).Select(_15_j);
          RAST._IType _17_formalType;
          RAST._IType _out4;
          _out4 = (this).GenType(((_16_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _17_formalType = _out4;
          _9_usedTypeParams = (this).GatherTypeParamNames(_9_usedTypeParams, _17_formalType);
          Dafny.ISequence<Dafny.Rune> _18_formalName;
          _18_formalName = DCOMP.__default.escapeVar(((_16_dtor).dtor_formal).dtor_name);
          if (((_15_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_18_formalName))) {
            _13_isNumeric = true;
          }
          if ((((_15_j).Sign != 0) && (_13_isNumeric)) && (!(Std.Strings.__default.OfNat(_15_j)).Equals(_18_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _18_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_15_j)));
            _13_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _12_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_12_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_18_formalName, RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_17_formalType))))));
          } else {
            _12_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_12_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_18_formalName, _17_formalType))));
          }
        }
        RAST._IFields _19_namedFields;
        _19_namedFields = RAST.Fields.create_NamedFields(_12_ctorArgs);
        if (_13_isNumeric) {
          _19_namedFields = (_19_namedFields).ToNamelessFields();
        }
        _5_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_5_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_11_ctor).dtor_name), _19_namedFields)));
      }
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _20_unusedTypeParams;
      _20_unusedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Helpers.Id<Func<Dafny.ISequence<RAST._ITypeParamDecl>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_21_rTypeParamsDecls) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
        foreach (RAST._ITypeParamDecl _compr_0 in (_21_rTypeParamsDecls).CloneAsArray()) {
          RAST._ITypeParamDecl _22_tp = (RAST._ITypeParamDecl)_compr_0;
          if ((_21_rTypeParamsDecls).Contains(_22_tp)) {
            _coll0.Add((_22_tp).dtor_name);
          }
        }
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll0);
      }))())(_2_rTypeParamsDecls), _9_usedTypeParams);
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _23_selfPath;
      _23_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _24_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _25_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out5;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out6;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_23_selfPath, _0_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_6_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _0_typeParamsSeq, out _out5, out _out6);
      _24_implBodyRaw = _out5;
      _25_traitBodies = _out6;
      Dafny.ISequence<RAST._IImplMember> _26_implBody;
      _26_implBody = _24_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _27_emittedFields;
      _27_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi2 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _28_i = BigInteger.Zero; _28_i < _hi2; _28_i++) {
        DAST._IDatatypeCtor _29_ctor;
        _29_ctor = ((c).dtor_ctors).Select(_28_i);
        BigInteger _hi3 = new BigInteger(((_29_ctor).dtor_args).Count);
        for (BigInteger _30_j = BigInteger.Zero; _30_j < _hi3; _30_j++) {
          DAST._IDatatypeDtor _31_dtor;
          _31_dtor = ((_29_ctor).dtor_args).Select(_30_j);
          Dafny.ISequence<Dafny.Rune> _32_callName;
          _32_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_31_dtor).dtor_callName, DCOMP.__default.escapeVar(((_31_dtor).dtor_formal).dtor_name));
          if (!((_27_emittedFields).Contains(_32_callName))) {
            _27_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_27_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_32_callName));
            RAST._IType _33_formalType;
            RAST._IType _out7;
            _out7 = (this).GenType(((_31_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _33_formalType = _out7;
            Dafny.ISequence<RAST._IMatchCase> _34_cases;
            _34_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi4 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _35_k = BigInteger.Zero; _35_k < _hi4; _35_k++) {
              DAST._IDatatypeCtor _36_ctor2;
              _36_ctor2 = ((c).dtor_ctors).Select(_35_k);
              Dafny.ISequence<Dafny.Rune> _37_pattern;
              _37_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_36_ctor2).dtor_name));
              RAST._IExpr _38_rhs = RAST.Expr.Default();
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _39_hasMatchingField;
              _39_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _40_patternInner;
              _40_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _41_isNumeric;
              _41_isNumeric = false;
              BigInteger _hi5 = new BigInteger(((_36_ctor2).dtor_args).Count);
              for (BigInteger _42_l = BigInteger.Zero; _42_l < _hi5; _42_l++) {
                DAST._IDatatypeDtor _43_dtor2;
                _43_dtor2 = ((_36_ctor2).dtor_args).Select(_42_l);
                Dafny.ISequence<Dafny.Rune> _44_patternName;
                _44_patternName = DCOMP.__default.escapeVar(((_43_dtor2).dtor_formal).dtor_name);
                if (((_42_l).Sign == 0) && ((_44_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _41_isNumeric = true;
                }
                if (_41_isNumeric) {
                  _44_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_43_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_42_l)));
                }
                if (object.Equals(((_31_dtor).dtor_formal).dtor_name, ((_43_dtor2).dtor_formal).dtor_name)) {
                  _39_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_44_patternName);
                }
                _40_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_40_patternInner, _44_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_41_isNumeric) {
                _37_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_37_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _40_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _37_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_37_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _40_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_39_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _38_rhs = (((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ops"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Deref"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"))).Apply1(RAST.__default.Borrow((RAST.Expr.create_Identifier((_39_hasMatchingField).dtor_value)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))));
                } else {
                  _38_rhs = RAST.Expr.create_Identifier((_39_hasMatchingField).dtor_value);
                }
              } else {
                _38_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _45_ctorMatch;
              _45_ctorMatch = RAST.MatchCase.create(_37_pattern, _38_rhs);
              _34_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_34_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_45_ctorMatch));
            }
            if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_20_unusedTypeParams).Count)).Sign == 1)) {
              _34_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_34_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            }
            RAST._IExpr _46_methodBody;
            _46_methodBody = RAST.Expr.create_Match(RAST.__default.self, _34_cases);
            _26_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_26_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_32_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_33_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_46_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _47_coerceTypes;
      _47_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _48_rCoerceTypeParams;
      _48_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _49_coerceArguments;
      _49_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _50_coerceMap;
      _50_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _51_rCoerceMap;
      _51_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _52_coerceMapToArg;
      _52_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _53_types;
        _53_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi6 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _54_typeI = BigInteger.Zero; _54_typeI < _hi6; _54_typeI++) {
          DAST._ITypeArgDecl _55_typeParam;
          _55_typeParam = ((c).dtor_typeParams).Select(_54_typeI);
          DAST._IType _56_typeArg;
          RAST._ITypeParamDecl _57_rTypeParamDecl;
          DAST._IType _out8;
          RAST._ITypeParamDecl _out9;
          (this).GenTypeParam(_55_typeParam, out _out8, out _out9);
          _56_typeArg = _out8;
          _57_rTypeParamDecl = _out9;
          RAST._IType _58_rTypeArg;
          RAST._IType _out10;
          _out10 = (this).GenType(_56_typeArg, DCOMP.GenTypeContext.@default());
          _58_rTypeArg = _out10;
          _53_types = Dafny.Sequence<RAST._IType>.Concat(_53_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_58_rTypeArg))));
          if (((_54_typeI) < (new BigInteger((_6_variances).Count))) && (((_6_variances).Select(_54_typeI)).is_Nonvariant)) {
            _47_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_47_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_58_rTypeArg));
            goto continue_2_0;
          }
          DAST._ITypeArgDecl _59_coerceTypeParam;
          DAST._ITypeArgDecl _60_dt__update__tmp_h0 = _55_typeParam;
          Dafny.ISequence<Dafny.Rune> _61_dt__update_hname_h0 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_54_typeI));
          _59_coerceTypeParam = DAST.TypeArgDecl.create(_61_dt__update_hname_h0, (_60_dt__update__tmp_h0).dtor_bounds, (_60_dt__update__tmp_h0).dtor_variance);
          DAST._IType _62_coerceTypeArg;
          RAST._ITypeParamDecl _63_rCoerceTypeParamDecl;
          DAST._IType _out11;
          RAST._ITypeParamDecl _out12;
          (this).GenTypeParam(_59_coerceTypeParam, out _out11, out _out12);
          _62_coerceTypeArg = _out11;
          _63_rCoerceTypeParamDecl = _out12;
          _50_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_50_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_56_typeArg, _62_coerceTypeArg)));
          RAST._IType _64_rCoerceType;
          RAST._IType _out13;
          _out13 = (this).GenType(_62_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _64_rCoerceType = _out13;
          _51_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_51_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_58_rTypeArg, _64_rCoerceType)));
          _47_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_47_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_64_rCoerceType));
          _48_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_48_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_63_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _65_coerceFormal;
          _65_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_54_typeI));
          _52_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_52_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_58_rTypeArg, _64_rCoerceType), (RAST.Expr.create_Identifier(_65_coerceFormal)).Clone())));
          _49_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_49_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_65_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_58_rTypeArg), _64_rCoerceType)), RAST.__default.StaticTrait)))));
        continue_2_0: ;
        }
      after_2_0: ;
        if ((new BigInteger((_20_unusedTypeParams).Count)).Sign == 1) {
          _5_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_5_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_66_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _66_tpe);
})), _53_types)))));
        }
      }
      bool _67_cIsEq;
      _67_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_67_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _4_datatypeName, _2_rTypeParamsDecls, _5_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), _3_whereConstraints, _26_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _68_printImplBodyCases;
      _68_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _69_hashImplBodyCases;
      _69_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _70_coerceImplBodyCases;
      _70_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _71_i = BigInteger.Zero; _71_i < _hi7; _71_i++) {
        DAST._IDatatypeCtor _72_ctor;
        _72_ctor = ((c).dtor_ctors).Select(_71_i);
        Dafny.ISequence<Dafny.Rune> _73_ctorMatch;
        _73_ctorMatch = DCOMP.__default.escapeName((_72_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _74_modulePrefix;
        if (((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) {
          _74_modulePrefix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        } else {
          _74_modulePrefix = Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."));
        }
        Dafny.ISequence<Dafny.Rune> _75_ctorName;
        _75_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_74_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_72_ctor).dtor_name));
        if (((new BigInteger((_75_ctorName).Count)) >= (new BigInteger(13))) && (((_75_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _75_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _76_printRhs;
        _76_printRhs = (this).writeStr(Dafny.Sequence<Dafny.Rune>.Concat(_75_ctorName, (((_72_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), false);
        RAST._IExpr _77_hashRhs;
        _77_hashRhs = (this).InitEmptyExpr();
        Dafny.ISequence<RAST._IAssignIdentifier> _78_coerceRhsArgs;
        _78_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _79_isNumeric;
        _79_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _80_ctorMatchInner;
        _80_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi8 = new BigInteger(((_72_ctor).dtor_args).Count);
        for (BigInteger _81_j = BigInteger.Zero; _81_j < _hi8; _81_j++) {
          DAST._IDatatypeDtor _82_dtor;
          _82_dtor = ((_72_ctor).dtor_args).Select(_81_j);
          Dafny.ISequence<Dafny.Rune> _83_patternName;
          _83_patternName = DCOMP.__default.escapeVar(((_82_dtor).dtor_formal).dtor_name);
          DAST._IType _84_formalType;
          _84_formalType = ((_82_dtor).dtor_formal).dtor_typ;
          if (((_81_j).Sign == 0) && ((_83_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _79_isNumeric = true;
          }
          if (_79_isNumeric) {
            _83_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_82_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_81_j)));
          }
          if ((_84_formalType).is_Arrow) {
            _77_hashRhs = (_77_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          } else {
            _77_hashRhs = (_77_hashRhs).Then((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_83_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))));
          }
          _80_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_80_ctorMatchInner, _83_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_81_j).Sign == 1) {
            _76_printRhs = (_76_printRhs).Then((this).writeStr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "), false));
          }
          _76_printRhs = (_76_printRhs).Then((((_84_formalType).is_Arrow) ? ((this).writeStr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<function>"), false)) : (RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"), ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_83_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter")), RAST.Expr.create_LiteralBool(false))), DAST.Format.UnaryOpFormat.create_NoFormat()))));
          RAST._IExpr _85_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _86_formalTpe;
          RAST._IType _out14;
          _out14 = (this).GenType(_84_formalType, DCOMP.GenTypeContext.@default());
          _86_formalTpe = _out14;
          DAST._IType _87_newFormalType;
          _87_newFormalType = (_84_formalType).Replace(_50_coerceMap);
          RAST._IType _88_newFormalTpe;
          _88_newFormalTpe = (_86_formalTpe).ReplaceMap(_51_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _89_upcastConverter;
          _89_upcastConverter = (this).UpcastConversionLambda(_84_formalType, _86_formalTpe, _87_newFormalType, _88_newFormalTpe, _52_coerceMapToArg);
          if ((_89_upcastConverter).is_Success) {
            RAST._IExpr _90_coercionFunction;
            _90_coercionFunction = (_89_upcastConverter).dtor_value;
            _85_coerceRhsArg = (_90_coercionFunction).Apply1(RAST.Expr.create_Identifier(_83_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_81_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _4_datatypeName));
            _85_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _78_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_78_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_83_patternName, _85_coerceRhsArg)));
        }
        RAST._IExpr _91_coerceRhs;
        _91_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_4_datatypeName)).FSel(DCOMP.__default.escapeName((_72_ctor).dtor_name)), _78_coerceRhsArgs);
        if (_79_isNumeric) {
          _73_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_73_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _80_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _73_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_73_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _80_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_72_ctor).dtor_hasAnyArgs) {
          _76_printRhs = (_76_printRhs).Then((this).writeStr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"), false));
        }
        _76_printRhs = (_76_printRhs).Then((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements()))));
        _68_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_68_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _73_ctorMatch), RAST.Expr.create_Block(_76_printRhs))));
        _69_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_69_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _73_ctorMatch), RAST.Expr.create_Block(_77_hashRhs))));
        _70_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_70_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _73_ctorMatch), RAST.Expr.create_Block(_91_coerceRhs))));
      }
      if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_20_unusedTypeParams).Count)).Sign == 1)) {
        Dafny.ISequence<RAST._IMatchCase> _92_extraCases;
        _92_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_Block((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
        _68_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_68_printImplBodyCases, _92_extraCases);
        _69_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_69_hashImplBodyCases, _92_extraCases);
        _70_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_70_coerceImplBodyCases, _92_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _93_defaultConstrainedTypeParams;
      _93_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _94_rTypeParamsDeclsWithEq;
      _94_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _95_rTypeParamsDeclsWithHash;
      _95_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _96_printImplBody;
      _96_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _68_printImplBodyCases);
      RAST._IExpr _97_hashImplBody;
      _97_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _69_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug"))).AsType(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType()))), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_96_printImplBody))))))));
      if ((new BigInteger((_48_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _98_coerceImplBody;
        _98_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _70_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _48_rCoerceTypeParams, _49_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _47_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _47_coerceTypes)), _98_coerceImplBody))))))))));
      }
      if ((new BigInteger((_8_singletonConstructors).Count)) == (new BigInteger(((c).dtor_ctors).Count))) {
        RAST._IType _99_datatypeType;
        _99_datatypeType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams);
        RAST._IType _100_instantiationType;
        if ((this).IsRcWrapped((c).dtor_attributes)) {
          _100_instantiationType = RAST.__default.Rc(_99_datatypeType);
        } else {
          _100_instantiationType = _99_datatypeType;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, _99_datatypeType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_AllSingletonConstructors"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SequenceIter"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_100_instantiationType))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_8_singletonConstructors)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply0()))))))));
      }
      if (_67_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_94_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_95_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))).AsType()))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_97_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _101_structName;
        _101_structName = (RAST.Expr.create_Identifier(_4_datatypeName)).FSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _102_structAssignments;
        _102_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi9 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _103_i = BigInteger.Zero; _103_i < _hi9; _103_i++) {
          DAST._IDatatypeDtor _104_dtor;
          _104_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_103_i);
          _102_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_102_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(((_104_dtor).dtor_formal).dtor_name), (((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).Apply0())));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _105_defaultConstrainedTypeParams;
        _105_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _106_fullType;
        _106_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _1_rTypeParams);
        if (_67_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_105_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _106_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_106_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_101_structName, _102_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsType()).Apply1(_106_fullType), RAST.Type.create_Borrowed(_106_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
      }
      return s;
    }
    public static RAST._IPath GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IPath r = RAST.Path.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        r = RAST.Path.create_Self();
        return r;
      } else {
        if (((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) {
          r = RAST.Path.create_Global();
        } else if (((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))) {
          r = RAST.__default.dafny__runtime;
        } else {
          r = RAST.Path.create_Crate();
        }
        BigInteger _hi0 = new BigInteger((p).Count);
        for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
          Dafny.ISequence<Dafny.Rune> _1_name;
          _1_name = ((p).Select(_0_i));
          if (escape) {
            _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs0 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName(_1_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2_modules = _let_tmp_rhs0.dtor__0;
            Dafny.ISequence<Dafny.Rune> _3_finalName = _let_tmp_rhs0.dtor__1;
            BigInteger _hi1 = new BigInteger((_2_modules).Count);
            for (BigInteger _4_j = BigInteger.Zero; _4_j < _hi1; _4_j++) {
              r = (r).MSel(DCOMP.__default.escapeName(((_2_modules).Select(_4_j))));
            }
            r = (r).MSel(DCOMP.__default.escapeName(_3_finalName));
          } else {
            r = (r).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1_name)));
          }
        }
      }
      return r;
    }
    public static RAST._IType GenPathType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType t = RAST.Type.Default();
      RAST._IPath _0_p;
      RAST._IPath _out0;
      _out0 = DCOMP.COMP.GenPath(p, true);
      _0_p = _out0;
      t = (_0_p).AsType();
      return t;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr e = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        e = RAST.__default.self;
        return e;
      }
      RAST._IPath _0_p;
      RAST._IPath _out0;
      _out0 = DCOMP.COMP.GenPath(p, escape);
      _0_p = _out0;
      e = (_0_p).AsExpr();
      return e;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi0 = new BigInteger((args).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        RAST._IType _1_genTp;
        RAST._IType _out0;
        _out0 = (this).GenType((args).Select(_0_i), genTypeContext);
        _1_genTp = _out0;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, bool genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source0 = c;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType _0_resolved = _source0.dtor_resolved;
          {
            RAST._IType _1_t;
            RAST._IType _out0;
            _out0 = DCOMP.COMP.GenPathType((_0_resolved).dtor_path);
            _1_t = _out0;
            Dafny.ISequence<RAST._IType> _2_typeArgs;
            Dafny.ISequence<RAST._IType> _out1;
            _out1 = (this).GenTypeArgs((_0_resolved).dtor_typeArgs, false);
            _2_typeArgs = _out1;
            s = RAST.Type.create_TypeApp(_1_t, _2_typeArgs);
            DAST._IResolvedTypeBase _source1 = (_0_resolved).dtor_kind;
            {
              if (_source1.is_Class) {
                {
                  s = (this).Object(s);
                }
                goto after_match1;
              }
            }
            {
              if (_source1.is_Datatype) {
                {
                  if ((this).IsRcWrapped((_0_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
                goto after_match1;
              }
            }
            {
              if (_source1.is_Trait) {
                {
                  if (((_0_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.AnyTrait;
                  }
                  if (!((genTypeContext))) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
                goto after_match1;
              }
            }
            {
              DAST._IType _3_base = _source1.dtor_baseType;
              DAST._INewtypeRange _4_range = _source1.dtor_range;
              bool _5_erased = _source1.dtor_erase;
              {
                if (_5_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source2 = DCOMP.COMP.NewtypeRangeToRustType(_4_range);
                  {
                    if (_source2.is_Some) {
                      RAST._IType _6_v = _source2.dtor_value;
                      s = _6_v;
                      goto after_match2;
                    }
                  }
                  {
                    RAST._IType _7_underlying;
                    RAST._IType _out2;
                    _out2 = (this).GenType(_3_base, DCOMP.GenTypeContext.@default());
                    _7_underlying = _out2;
                    s = RAST.Type.create_TSynonym(s, _7_underlying);
                  }
                after_match2: ;
                }
              }
            }
          after_match1: ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Object) {
          {
            s = RAST.__default.AnyTrait;
            if (!((genTypeContext))) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<DAST._IType> _8_types = _source0.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IType> _9_args;
            _9_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _10_i;
            _10_i = BigInteger.Zero;
            while ((_10_i) < (new BigInteger((_8_types).Count))) {
              RAST._IType _11_generated;
              RAST._IType _out3;
              _out3 = (this).GenType((_8_types).Select(_10_i), false);
              _11_generated = _out3;
              _9_args = Dafny.Sequence<RAST._IType>.Concat(_9_args, Dafny.Sequence<RAST._IType>.FromElements(_11_generated));
              _10_i = (_10_i) + (BigInteger.One);
            }
            if ((new BigInteger((_8_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              s = RAST.Type.create_TupleType(_9_args);
            } else {
              s = RAST.__default.SystemTupleType(_9_args);
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Array) {
          DAST._IType _12_element = _source0.dtor_element;
          BigInteger _13_dims = _source0.dtor_dims;
          {
            if ((_13_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _14_elem;
              RAST._IType _out4;
              _out4 = (this).GenType(_12_element, false);
              _14_elem = _out4;
              if ((_13_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_14_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _15_n;
                _15_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_13_dims));
                s = (((RAST.__default.dafny__runtime).MSel(_15_n)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_14_elem));
                s = (this).Object(s);
              }
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Seq) {
          DAST._IType _16_element = _source0.dtor_element;
          {
            RAST._IType _17_elem;
            RAST._IType _out5;
            _out5 = (this).GenType(_16_element, false);
            _17_elem = _out5;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_17_elem));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Set) {
          DAST._IType _18_element = _source0.dtor_element;
          {
            RAST._IType _19_elem;
            RAST._IType _out6;
            _out6 = (this).GenType(_18_element, false);
            _19_elem = _out6;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_19_elem));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Multiset) {
          DAST._IType _20_element = _source0.dtor_element;
          {
            RAST._IType _21_elem;
            RAST._IType _out7;
            _out7 = (this).GenType(_20_element, false);
            _21_elem = _out7;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_21_elem));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Map) {
          DAST._IType _22_key = _source0.dtor_key;
          DAST._IType _23_value = _source0.dtor_value;
          {
            RAST._IType _24_keyType;
            RAST._IType _out8;
            _out8 = (this).GenType(_22_key, false);
            _24_keyType = _out8;
            RAST._IType _25_valueType;
            RAST._IType _out9;
            _out9 = (this).GenType(_23_value, genTypeContext);
            _25_valueType = _out9;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_24_keyType, _25_valueType));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapBuilder) {
          DAST._IType _26_key = _source0.dtor_key;
          DAST._IType _27_value = _source0.dtor_value;
          {
            RAST._IType _28_keyType;
            RAST._IType _out10;
            _out10 = (this).GenType(_26_key, false);
            _28_keyType = _out10;
            RAST._IType _29_valueType;
            RAST._IType _out11;
            _out11 = (this).GenType(_27_value, genTypeContext);
            _29_valueType = _out11;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_28_keyType, _29_valueType));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetBuilder) {
          DAST._IType _30_elem = _source0.dtor_element;
          {
            RAST._IType _31_elemType;
            RAST._IType _out12;
            _out12 = (this).GenType(_30_elem, false);
            _31_elemType = _out12;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_31_elemType));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Arrow) {
          Dafny.ISequence<DAST._IType> _32_args = _source0.dtor_args;
          DAST._IType _33_result = _source0.dtor_result;
          {
            Dafny.ISequence<RAST._IType> _34_argTypes;
            _34_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _35_i;
            _35_i = BigInteger.Zero;
            while ((_35_i) < (new BigInteger((_32_args).Count))) {
              RAST._IType _36_generated;
              RAST._IType _out13;
              _out13 = (this).GenType((_32_args).Select(_35_i), false);
              _36_generated = _out13;
              _34_argTypes = Dafny.Sequence<RAST._IType>.Concat(_34_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_36_generated)));
              _35_i = (_35_i) + (BigInteger.One);
            }
            RAST._IType _37_resultType;
            RAST._IType _out14;
            _out14 = (this).GenType(_33_result, DCOMP.GenTypeContext.@default());
            _37_resultType = _out14;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_34_argTypes, _37_resultType)));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source0.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _38_name = _h90;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_38_name));
          goto after_match0;
        }
      }
      {
        if (_source0.is_Primitive) {
          DAST._IPrimitive _39_p = _source0.dtor_Primitive_a0;
          {
            DAST._IPrimitive _source3 = _39_p;
            {
              if (_source3.is_Int) {
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).AsType();
                goto after_match3;
              }
            }
            {
              if (_source3.is_Real) {
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsType();
                goto after_match3;
              }
            }
            {
              if (_source3.is_String) {
                s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType()));
                goto after_match3;
              }
            }
            {
              if (_source3.is_Bool) {
                s = RAST.Type.create_Bool();
                goto after_match3;
              }
            }
            {
              s = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType();
            }
          after_match3: ;
          }
          goto after_match0;
        }
      }
      {
        Dafny.ISequence<Dafny.Rune> _40_v = _source0.dtor_Passthrough_a0;
        s = RAST.__default.RawType(_40_v);
      }
    after_match0: ;
      return s;
    }
    public bool EnclosingIsTrait(DAST._IType tpe) {
      return ((tpe).is_UserDefined) && ((((tpe).dtor_resolved).dtor_kind).is_Trait);
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _hi0 = new BigInteger((body).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        DAST._IMethod _source0 = (body).Select(_0_i);
        {
          DAST._IMethod _1_m = _source0;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source1 = (_1_m).dtor_overridingPath;
            {
              if (_source1.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2_p = _source1.dtor_value;
                {
                  Dafny.ISequence<RAST._IImplMember> _3_existing;
                  _3_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_2_p)) {
                    _3_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_2_p);
                  }
                  if (((new BigInteger(((_1_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _4_genMethod;
                  RAST._IImplMember _out0;
                  _out0 = (this).GenMethod(_1_m, true, enclosingType, enclosingTypeParams);
                  _4_genMethod = _out0;
                  _3_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_3_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_4_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_2_p, _3_existing)));
                }
                goto after_match1;
              }
            }
            {
              {
                RAST._IImplMember _5_generated;
                RAST._IImplMember _out1;
                _out1 = (this).GenMethod(_1_m, forTrait, enclosingType, enclosingTypeParams);
                _5_generated = _out1;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_5_generated));
              }
            }
          after_match1: ;
          }
        }
      after_match0: ;
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params, bool forLambda)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi0 = new BigInteger((@params).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        DAST._IFormal _1_param;
        _1_param = (@params).Select(_0_i);
        RAST._IType _2_paramType;
        RAST._IType _out0;
        _out0 = (this).GenType((_1_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _2_paramType = _out0;
        if (((!((_2_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _2_paramType = RAST.Type.create_Borrowed(_2_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1_param).dtor_name), _2_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _0_params;
      Dafny.ISequence<RAST._IFormal> _out0;
      _out0 = (this).GenParams((m).dtor_params, false);
      _0_params = _out0;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1_paramNames;
      _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2_paramTypes;
      _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi0 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _3_paramI = BigInteger.Zero; _3_paramI < _hi0; _3_paramI++) {
        DAST._IFormal _4_dafny__formal;
        _4_dafny__formal = ((m).dtor_params).Select(_3_paramI);
        RAST._IFormal _5_formal;
        _5_formal = (_0_params).Select(_3_paramI);
        Dafny.ISequence<Dafny.Rune> _6_name;
        _6_name = (_5_formal).dtor_name;
        _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_6_name));
        _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2_paramTypes, _6_name, (_5_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _7_fnName;
      _7_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _8_selfIdent;
      _8_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _9_selfId;
        _9_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _9_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv0 = enclosingTypeParams;
        DAST._IType _10_instanceType;
        DAST._IType _source0 = enclosingType;
        {
          if (_source0.is_UserDefined) {
            DAST._IResolvedType _11_r = _source0.dtor_resolved;
            _10_instanceType = DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_11_r, _pat_let20_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let20_0, _12_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv0, _pat_let21_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let21_0, _13_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_12_dt__update__tmp_h0).dtor_path, _13_dt__update_htypeArgs_h0, (_12_dt__update__tmp_h0).dtor_kind, (_12_dt__update__tmp_h0).dtor_attributes, (_12_dt__update__tmp_h0).dtor_properMethods, (_12_dt__update__tmp_h0).dtor_extendedTypes))))));
            goto after_match0;
          }
        }
        {
          _10_instanceType = enclosingType;
        }
      after_match0: ;
        if (forTrait) {
          RAST._IFormal _14_selfFormal;
          if (((m).dtor_wasFunction) && (((this).ObjectType).is_RawPointers)) {
            _14_selfFormal = RAST.Formal.selfBorrowed;
          } else {
            _14_selfFormal = RAST.Formal.selfBorrowedMut;
          }
          _0_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_14_selfFormal), _0_params);
        } else {
          RAST._IType _15_tpe;
          RAST._IType _out1;
          _out1 = (this).GenType(_10_instanceType, DCOMP.GenTypeContext.@default());
          _15_tpe = _out1;
          if ((_9_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            if (((this).ObjectType).is_RcMut) {
              _15_tpe = RAST.Type.create_Borrowed(_15_tpe);
            }
          } else if ((_9_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_15_tpe).IsObjectOrPointer()) {
              if (((m).dtor_wasFunction) && (((this).ObjectType).is_RawPointers)) {
                _15_tpe = RAST.__default.SelfBorrowed;
              } else {
                _15_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _15_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.__default.SelfOwned));
              } else {
                _15_tpe = RAST.Type.create_Borrowed(RAST.__default.SelfOwned);
              }
            }
          }
          _0_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_9_selfId, _15_tpe)), _0_params);
        }
        _8_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_9_selfId, _10_instanceType);
      }
      Dafny.ISequence<RAST._IType> _16_retTypeArgs;
      _16_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _17_typeI;
      _17_typeI = BigInteger.Zero;
      while ((_17_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _18_typeExpr;
        RAST._IType _out2;
        _out2 = (this).GenType(((m).dtor_outTypes).Select(_17_typeI), DCOMP.GenTypeContext.@default());
        _18_typeExpr = _out2;
        _16_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_16_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_18_typeExpr));
        _17_typeI = (_17_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _19_visibility;
      if (forTrait) {
        _19_visibility = RAST.Visibility.create_PRIV();
      } else {
        _19_visibility = RAST.Visibility.create_PUB();
      }
      Dafny.ISequence<DAST._ITypeArgDecl> _20_typeParamsFiltered;
      _20_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi1 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _21_typeParamI = BigInteger.Zero; _21_typeParamI < _hi1; _21_typeParamI++) {
        DAST._ITypeArgDecl _22_typeParam;
        _22_typeParam = ((m).dtor_typeParams).Select(_21_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_22_typeParam).dtor_name)))) {
          _20_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_20_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_22_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _23_typeParams;
      _23_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_20_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi2 = new BigInteger((_20_typeParamsFiltered).Count);
        for (BigInteger _24_i = BigInteger.Zero; _24_i < _hi2; _24_i++) {
          DAST._IType _25_typeArg;
          RAST._ITypeParamDecl _26_rTypeParamDecl;
          DAST._IType _out3;
          RAST._ITypeParamDecl _out4;
          (this).GenTypeParam((_20_typeParamsFiltered).Select(_24_i), out _out3, out _out4);
          _25_typeArg = _out3;
          _26_rTypeParamDecl = _out4;
          RAST._ITypeParamDecl _27_dt__update__tmp_h1 = _26_rTypeParamDecl;
          Dafny.ISequence<RAST._IType> _28_dt__update_hconstraints_h0 = (_26_rTypeParamDecl).dtor_constraints;
          _26_rTypeParamDecl = RAST.TypeParamDecl.create((_27_dt__update__tmp_h1).dtor_name, _28_dt__update_hconstraints_h0);
          _23_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_23_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_26_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _29_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _30_env = DCOMP.Environment.Default();
      RAST._IExpr _31_preBody;
      _31_preBody = (this).InitEmptyExpr();
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _32_preAssignNames;
      _32_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _33_preAssignTypes;
      _33_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _34_earlyReturn;
        _34_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source1 = (m).dtor_outVars;
        {
          if (_source1.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _35_outVars = _source1.dtor_value;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _34_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi3 = new BigInteger((_35_outVars).Count);
                for (BigInteger _36_outI = BigInteger.Zero; _36_outI < _hi3; _36_outI++) {
                  Dafny.ISequence<Dafny.Rune> _37_outVar;
                  _37_outVar = (_35_outVars).Select(_36_outI);
                  Dafny.ISequence<Dafny.Rune> _38_outName;
                  _38_outName = DCOMP.__default.escapeVar(_37_outVar);
                  Dafny.ISequence<Dafny.Rune> _39_tracker__name;
                  _39_tracker__name = DCOMP.__default.AddAssignedPrefix(_38_outName);
                  _32_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_32_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_39_tracker__name));
                  _33_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_33_preAssignTypes, _39_tracker__name, RAST.Type.create_Bool());
                  _31_preBody = (_31_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _39_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _40_tupleArgs;
                _40_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi4 = new BigInteger((_35_outVars).Count);
                for (BigInteger _41_outI = BigInteger.Zero; _41_outI < _hi4; _41_outI++) {
                  Dafny.ISequence<Dafny.Rune> _42_outVar;
                  _42_outVar = (_35_outVars).Select(_41_outI);
                  RAST._IType _43_outType;
                  RAST._IType _out5;
                  _out5 = (this).GenType(((m).dtor_outTypes).Select(_41_outI), DCOMP.GenTypeContext.@default());
                  _43_outType = _out5;
                  Dafny.ISequence<Dafny.Rune> _44_outName;
                  _44_outName = DCOMP.__default.escapeVar(_42_outVar);
                  _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_44_outName));
                  RAST._IType _45_outMaybeType;
                  if ((_43_outType).CanReadWithoutClone()) {
                    _45_outMaybeType = _43_outType;
                  } else {
                    _45_outMaybeType = RAST.__default.MaybePlaceboType(_43_outType);
                  }
                  _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2_paramTypes, _44_outName, _45_outMaybeType);
                  _40_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_40_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_44_outName));
                }
                _34_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_40_tupleArgs);
              }
            }
            goto after_match1;
          }
        }
        {
        }
      after_match1: ;
        _30_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_32_preAssignNames, _1_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_33_preAssignTypes, _2_paramTypes));
        RAST._IExpr _46_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _47___v71;
        DCOMP._IEnvironment _48___v72;
        RAST._IExpr _out6;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
        DCOMP._IEnvironment _out8;
        (this).GenStmts((m).dtor_body, _8_selfIdent, _30_env, true, _34_earlyReturn, out _out6, out _out7, out _out8);
        _46_body = _out6;
        _47___v71 = _out7;
        _48___v72 = _out8;
        _29_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_31_preBody).Then(_46_body));
      } else {
        _30_env = DCOMP.Environment.create(_1_paramNames, _2_paramTypes);
        _29_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_19_visibility, RAST.Fn.create(_7_fnName, _23_typeParams, _0_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_16_retTypeArgs).Count)) == (BigInteger.One)) ? ((_16_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_16_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _29_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = (this).InitEmptyExpr();
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _0_declarations;
      _0_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1_i;
      _1_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _2_stmts;
      _2_stmts = stmts;
      while ((_1_i) < (new BigInteger((_2_stmts).Count))) {
        DAST._IStatement _3_stmt;
        _3_stmt = (_2_stmts).Select(_1_i);
        DAST._IStatement _source0 = _3_stmt;
        {
          if (_source0.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _4_name = _source0.dtor_name;
            DAST._IType _5_optType = _source0.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source0.dtor_maybeValue;
            if (maybeValue0.is_None) {
              if (((_1_i) + (BigInteger.One)) < (new BigInteger((_2_stmts).Count))) {
                DAST._IStatement _source1 = (_2_stmts).Select((_1_i) + (BigInteger.One));
                {
                  if (_source1.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source1.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> _6_name2 = lhs0.dtor_ident;
                      DAST._IExpression _7_rhs = _source1.dtor_value;
                      if (object.Equals(_6_name2, _4_name)) {
                        _2_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_2_stmts).Subsequence(BigInteger.Zero, _1_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_4_name, _5_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_7_rhs)))), (_2_stmts).Drop((_1_i) + (new BigInteger(2))));
                        _3_stmt = (_2_stmts).Select(_1_i);
                      }
                      goto after_match1;
                    }
                  }
                }
                {
                }
              after_match1: ;
              }
              goto after_match0;
            }
          }
        }
        {
        }
      after_match0: ;
        RAST._IExpr _8_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _9_recIdents;
        DCOMP._IEnvironment _10_newEnv2;
        RAST._IExpr _out0;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1;
        DCOMP._IEnvironment _out2;
        (this).GenStmt(_3_stmt, selfIdent, newEnv, (isLast) && ((_1_i) == ((new BigInteger((_2_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out0, out _out1, out _out2);
        _8_stmtExpr = _out0;
        _9_recIdents = _out1;
        _10_newEnv2 = _out2;
        newEnv = _10_newEnv2;
        DAST._IStatement _source2 = _3_stmt;
        {
          if (_source2.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _11_name = _source2.dtor_name;
            {
              _0_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_0_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_11_name)));
            }
            goto after_match2;
          }
        }
        {
        }
      after_match2: ;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_9_recIdents, _0_declarations));
        generated = (generated).Then(_8_stmtExpr);
        _1_i = (_1_i) + (BigInteger.One);
        if ((_8_stmtExpr).is_Return) {
          goto after_0;
        }
      continue_0: ;
      }
    after_0: ;
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source0 = lhs;
      {
        if (_source0.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _0_id = _source0.dtor_ident;
          {
            Dafny.ISequence<Dafny.Rune> _1_idRust;
            _1_idRust = DCOMP.__default.escapeVar(_0_id);
            if (((env).IsBorrowed(_1_idRust)) || ((env).IsBorrowedMut(_1_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1_idRust);
            needsIIFE = false;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Select) {
          DAST._IExpression _2_on = _source0.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _3_field = _source0.dtor_field;
          {
            Dafny.ISequence<Dafny.Rune> _4_fieldName;
            _4_fieldName = DCOMP.__default.escapeVar(_3_field);
            RAST._IExpr _5_onExpr;
            DCOMP._IOwnership _6_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _7_recIdents;
            RAST._IExpr _out0;
            DCOMP._IOwnership _out1;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
            (this).GenExpr(_2_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out0, out _out1, out _out2);
            _5_onExpr = _out0;
            _6_onOwned = _out1;
            _7_recIdents = _out2;
            RAST._IExpr _source1 = _5_onExpr;
            {
              bool disjunctiveMatch0 = false;
              if (_source1.is_Call) {
                RAST._IExpr obj0 = _source1.dtor_obj;
                if (obj0.is_Select) {
                  RAST._IExpr obj1 = obj0.dtor_obj;
                  if (obj1.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name0 = obj1.dtor_name;
                    if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name1 = obj0.dtor_name;
                      if (object.Equals(name1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        disjunctiveMatch0 = true;
                      }
                    }
                  }
                }
              }
              if (_source1.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name2 = _source1.dtor_name;
                if (object.Equals(name2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch0 = true;
                }
              }
              if (_source1.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op10 = _source1.dtor_op1;
                if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying0 = _source1.dtor_underlying;
                  if (underlying0.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name3 = underlying0.dtor_name;
                    if (object.Equals(name3, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch0 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch0) {
                Dafny.ISequence<Dafny.Rune> _8_isAssignedVar;
                _8_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_4_fieldName);
                if (((newEnv).dtor_names).Contains(_8_isAssignedVar)) {
                  generated = (((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_4_fieldName), RAST.Expr.create_Identifier(_8_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_8_isAssignedVar);
                } else {
                  generated = RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_SelectMember(((this).modify__macro).Apply1((this).thisInConstructor), _4_fieldName)), rhs);
                }
                goto after_match1;
              }
            }
            {
              if (!object.Equals(_5_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _5_onExpr = ((this).modify__macro).Apply1(_5_onExpr);
              }
              generated = RAST.__default.AssignMember(_5_onExpr, _4_fieldName, rhs);
            }
          after_match1: ;
            readIdents = _7_recIdents;
            needsIIFE = false;
          }
          goto after_match0;
        }
      }
      {
        DAST._IExpression _9_on = _source0.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _10_indices = _source0.dtor_indices;
        {
          RAST._IExpr _11_onExpr;
          DCOMP._IOwnership _12_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _13_recIdents;
          RAST._IExpr _out3;
          DCOMP._IOwnership _out4;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
          (this).GenExpr(_9_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out3, out _out4, out _out5);
          _11_onExpr = _out3;
          _12_onOwned = _out4;
          _13_recIdents = _out5;
          readIdents = _13_recIdents;
          _11_onExpr = ((this).modify__macro).Apply1(_11_onExpr);
          RAST._IExpr _14_r;
          _14_r = (this).InitEmptyExpr();
          Dafny.ISequence<RAST._IExpr> _15_indicesExpr;
          _15_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi0 = new BigInteger((_10_indices).Count);
          for (BigInteger _16_i = BigInteger.Zero; _16_i < _hi0; _16_i++) {
            RAST._IExpr _17_idx;
            DCOMP._IOwnership _18___v81;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _19_recIdentsIdx;
            RAST._IExpr _out6;
            DCOMP._IOwnership _out7;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out8;
            (this).GenExpr((_10_indices).Select(_16_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out6, out _out7, out _out8);
            _17_idx = _out6;
            _18___v81 = _out7;
            _19_recIdentsIdx = _out8;
            Dafny.ISequence<Dafny.Rune> _20_varName;
            _20_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_16_i));
            _15_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_15_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_20_varName)));
            _14_r = (_14_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _20_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_17_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _19_recIdentsIdx);
          }
          if ((new BigInteger((_10_indices).Count)) > (BigInteger.One)) {
            _11_onExpr = (_11_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          generated = (_14_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_11_onExpr, _15_indicesExpr)), rhs));
          needsIIFE = true;
        }
      }
    after_match0: ;
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source0 = stmt;
      {
        if (_source0.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _0_fields = _source0.dtor_fields;
          {
            generated = (this).InitEmptyExpr();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi0 = new BigInteger((_0_fields).Count);
            for (BigInteger _1_i = BigInteger.Zero; _1_i < _hi0; _1_i++) {
              DAST._IFormal _2_field;
              _2_field = (_0_fields).Select(_1_i);
              Dafny.ISequence<Dafny.Rune> _3_fieldName;
              _3_fieldName = DCOMP.__default.escapeVar((_2_field).dtor_name);
              RAST._IType _4_fieldTyp;
              RAST._IType _out0;
              _out0 = (this).GenType((_2_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _4_fieldTyp = _out0;
              Dafny.ISequence<Dafny.Rune> _5_isAssignedVar;
              _5_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_3_fieldName);
              if (((newEnv).dtor_names).Contains(_5_isAssignedVar)) {
                RAST._IExpr _6_rhs;
                DCOMP._IOwnership _7___v82;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _8___v83;
                RAST._IExpr _out1;
                DCOMP._IOwnership _out2;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out3;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_2_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1, out _out2, out _out3);
                _6_rhs = _out1;
                _7___v82 = _out2;
                _8___v83 = _out3;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5_isAssignedVar));
                generated = (generated).Then((((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_3_fieldName), RAST.Expr.create_Identifier(_5_isAssignedVar), _6_rhs)));
                newEnv = (newEnv).RemoveAssigned(_5_isAssignedVar);
              }
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _9_name = _source0.dtor_name;
          DAST._IType _10_typ = _source0.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source0.dtor_maybeValue;
          if (maybeValue0.is_Some) {
            DAST._IExpression _11_expression = maybeValue0.dtor_value;
            {
              RAST._IType _12_tpe;
              RAST._IType _out4;
              _out4 = (this).GenType(_10_typ, DCOMP.GenTypeContext.@default());
              _12_tpe = _out4;
              Dafny.ISequence<Dafny.Rune> _13_varName;
              _13_varName = DCOMP.__default.escapeVar(_9_name);
              bool _14_hasCopySemantics;
              _14_hasCopySemantics = (_12_tpe).CanReadWithoutClone();
              if (((_11_expression).is_InitializationValue) && (!(_14_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _13_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.MaybePlaceboPath).AsExpr()).ApplyType1(_12_tpe)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply0()));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_13_varName, RAST.__default.MaybePlaceboType(_12_tpe));
              } else {
                RAST._IExpr _15_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _16_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_11_expression).is_InitializationValue) && ((_12_tpe).IsObjectOrPointer())) {
                  _15_expr = (_12_tpe).ToNullExpr();
                  _16_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _17_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out5;
                  DCOMP._IOwnership _out6;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
                  (this).GenExpr(_11_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out5, out _out6, out _out7);
                  _15_expr = _out5;
                  _17_exprOwnership = _out6;
                  _16_recIdents = _out7;
                }
                readIdents = _16_recIdents;
                if ((_11_expression).is_NewUninitArray) {
                  _12_tpe = (_12_tpe).TypeAtInitialization();
                } else {
                  _12_tpe = _12_tpe;
                }
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _13_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_12_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_15_expr));
                newEnv = (env).AddAssigned(_13_varName, _12_tpe);
              }
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _18_name = _source0.dtor_name;
          DAST._IType _19_typ = _source0.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source0.dtor_maybeValue;
          if (maybeValue1.is_None) {
            {
              DAST._IStatement _20_newStmt;
              _20_newStmt = DAST.Statement.create_DeclareVar(_18_name, _19_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_19_typ)));
              RAST._IExpr _out8;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out9;
              DCOMP._IEnvironment _out10;
              (this).GenStmt(_20_newStmt, selfIdent, env, isLast, earlyReturn, out _out8, out _out9, out _out10);
              generated = _out8;
              readIdents = _out9;
              newEnv = _out10;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Assign) {
          DAST._IAssignLhs _21_lhs = _source0.dtor_lhs;
          DAST._IExpression _22_expression = _source0.dtor_value;
          {
            RAST._IExpr _23_exprGen;
            DCOMP._IOwnership _24___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _25_exprIdents;
            RAST._IExpr _out11;
            DCOMP._IOwnership _out12;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out13;
            (this).GenExpr(_22_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out11, out _out12, out _out13);
            _23_exprGen = _out11;
            _24___v84 = _out12;
            _25_exprIdents = _out13;
            if ((_21_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _26_rustId;
              _26_rustId = DCOMP.__default.escapeVar((_21_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _27_tpe;
              _27_tpe = (env).GetType(_26_rustId);
              if (((_27_tpe).is_Some) && ((((_27_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _23_exprGen = RAST.__default.MaybePlacebo(_23_exprGen);
              }
            }
            if (((_21_lhs).is_Index) && (((_21_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _28_rustId;
              _28_rustId = DCOMP.__default.escapeVar(((_21_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _29_tpe;
              _29_tpe = (env).GetType(_28_rustId);
              if (((_29_tpe).is_Some) && ((((_29_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _23_exprGen = RAST.__default.MaybeUninitNew(_23_exprGen);
              }
            }
            RAST._IExpr _30_lhsGen;
            bool _31_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _32_recIdents;
            DCOMP._IEnvironment _33_resEnv;
            RAST._IExpr _out14;
            bool _out15;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out16;
            DCOMP._IEnvironment _out17;
            (this).GenAssignLhs(_21_lhs, _23_exprGen, selfIdent, env, out _out14, out _out15, out _out16, out _out17);
            _30_lhsGen = _out14;
            _31_needsIIFE = _out15;
            _32_recIdents = _out16;
            _33_resEnv = _out17;
            generated = _30_lhsGen;
            newEnv = _33_resEnv;
            if (_31_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_32_recIdents, _25_exprIdents);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_If) {
          DAST._IExpression _34_cond = _source0.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _35_thnDafny = _source0.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _36_elsDafny = _source0.dtor_els;
          {
            RAST._IExpr _37_cond;
            DCOMP._IOwnership _38___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _39_recIdents;
            RAST._IExpr _out18;
            DCOMP._IOwnership _out19;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out20;
            (this).GenExpr(_34_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out18, out _out19, out _out20);
            _37_cond = _out18;
            _38___v85 = _out19;
            _39_recIdents = _out20;
            Dafny.ISequence<Dafny.Rune> _40_condString;
            _40_condString = (_37_cond)._ToString(DCOMP.__default.IND);
            readIdents = _39_recIdents;
            RAST._IExpr _41_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _42_thnIdents;
            DCOMP._IEnvironment _43_thnEnv;
            RAST._IExpr _out21;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out22;
            DCOMP._IEnvironment _out23;
            (this).GenStmts(_35_thnDafny, selfIdent, env, isLast, earlyReturn, out _out21, out _out22, out _out23);
            _41_thn = _out21;
            _42_thnIdents = _out22;
            _43_thnEnv = _out23;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _42_thnIdents);
            RAST._IExpr _44_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _45_elsIdents;
            DCOMP._IEnvironment _46_elsEnv;
            RAST._IExpr _out24;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out25;
            DCOMP._IEnvironment _out26;
            (this).GenStmts(_36_elsDafny, selfIdent, env, isLast, earlyReturn, out _out24, out _out25, out _out26);
            _44_els = _out24;
            _45_elsIdents = _out25;
            _46_elsEnv = _out26;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _45_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_37_cond, _41_thn, _44_els);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _47_lbl = _source0.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _48_body = _source0.dtor_body;
          {
            RAST._IExpr _49_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _50_bodyIdents;
            DCOMP._IEnvironment _51_env2;
            RAST._IExpr _out27;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out28;
            DCOMP._IEnvironment _out29;
            (this).GenStmts(_48_body, selfIdent, env, isLast, earlyReturn, out _out27, out _out28, out _out29);
            _49_body = _out27;
            _50_bodyIdents = _out28;
            _51_env2 = _out29;
            readIdents = _50_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _47_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_49_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_While) {
          DAST._IExpression _52_cond = _source0.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _53_body = _source0.dtor_body;
          {
            RAST._IExpr _54_cond;
            DCOMP._IOwnership _55___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _56_recIdents;
            RAST._IExpr _out30;
            DCOMP._IOwnership _out31;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
            (this).GenExpr(_52_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
            _54_cond = _out30;
            _55___v86 = _out31;
            _56_recIdents = _out32;
            readIdents = _56_recIdents;
            RAST._IExpr _57_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _58_bodyIdents;
            DCOMP._IEnvironment _59_bodyEnv;
            RAST._IExpr _out33;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out34;
            DCOMP._IEnvironment _out35;
            (this).GenStmts(_53_body, selfIdent, env, false, earlyReturn, out _out33, out _out34, out _out35);
            _57_bodyExpr = _out33;
            _58_bodyIdents = _out34;
            _59_bodyEnv = _out35;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _58_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_54_cond), _57_bodyExpr);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _60_boundName = _source0.dtor_boundName;
          DAST._IType _61_boundType = _source0.dtor_boundType;
          DAST._IExpression _62_overExpr = _source0.dtor_over;
          Dafny.ISequence<DAST._IStatement> _63_body = _source0.dtor_body;
          {
            RAST._IExpr _64_over;
            DCOMP._IOwnership _65___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _66_recIdents;
            RAST._IExpr _out36;
            DCOMP._IOwnership _out37;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out38;
            (this).GenExpr(_62_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out36, out _out37, out _out38);
            _64_over = _out36;
            _65___v87 = _out37;
            _66_recIdents = _out38;
            if (((_62_overExpr).is_MapBoundedPool) || ((_62_overExpr).is_SetBoundedPool)) {
              _64_over = ((_64_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply0();
            }
            RAST._IType _67_boundTpe;
            RAST._IType _out39;
            _out39 = (this).GenType(_61_boundType, DCOMP.GenTypeContext.@default());
            _67_boundTpe = _out39;
            readIdents = _66_recIdents;
            Dafny.ISequence<Dafny.Rune> _68_boundRName;
            _68_boundRName = DCOMP.__default.escapeVar(_60_boundName);
            RAST._IExpr _69_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _70_bodyIdents;
            DCOMP._IEnvironment _71_bodyEnv;
            RAST._IExpr _out40;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out41;
            DCOMP._IEnvironment _out42;
            (this).GenStmts(_63_body, selfIdent, (env).AddAssigned(_68_boundRName, _67_boundTpe), false, earlyReturn, out _out40, out _out41, out _out42);
            _69_bodyExpr = _out40;
            _70_bodyIdents = _out41;
            _71_bodyEnv = _out42;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _70_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_68_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_68_boundRName, _64_over, _69_bodyExpr);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _72_toLabel = _source0.dtor_toLabel;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source1 = _72_toLabel;
            {
              if (_source1.is_Some) {
                Dafny.ISequence<Dafny.Rune> _73_lbl = _source1.dtor_value;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _73_lbl)));
                }
                goto after_match1;
              }
            }
            {
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
          after_match1: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _74_body = _source0.dtor_body;
          {
            generated = (this).InitEmptyExpr();
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _75_selfClone;
              DCOMP._IOwnership _76___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _77___v89;
              RAST._IExpr _out43;
              DCOMP._IOwnership _out44;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out45;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out43, out _out44, out _out45);
              _75_selfClone = _out43;
              _76___v88 = _out44;
              _77___v89 = _out45;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_75_selfClone)));
            }
            newEnv = env;
            RAST._IExpr _78_loopBegin;
            _78_loopBegin = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi1 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _79_paramI = BigInteger.Zero; _79_paramI < _hi1; _79_paramI++) {
              Dafny.ISequence<Dafny.Rune> _80_param;
              _80_param = ((env).dtor_names).Select(_79_paramI);
              if ((_80_param).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_accumulator"))) {
                goto continue_4_0;
              }
              RAST._IExpr _81_paramInit;
              DCOMP._IOwnership _82___v90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _83___v91;
              RAST._IExpr _out46;
              DCOMP._IOwnership _out47;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out48;
              (this).GenIdent(_80_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out46, out _out47, out _out48);
              _81_paramInit = _out46;
              _82___v90 = _out47;
              _83___v91 = _out48;
              Dafny.ISequence<Dafny.Rune> _84_recVar;
              _84_recVar = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.COMP.TailRecursionPrefix, Std.Strings.__default.OfNat(_79_paramI));
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _84_recVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_81_paramInit)));
              if (((env).dtor_types).Contains(_80_param)) {
                RAST._IType _85_declaredType;
                _85_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_80_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_80_param, _85_declaredType);
                newEnv = (newEnv).AddAssigned(_84_recVar, _85_declaredType);
              }
              _78_loopBegin = (_78_loopBegin).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _80_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Identifier(_84_recVar))));
            continue_4_0: ;
            }
          after_4_0: ;
            RAST._IExpr _86_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _87_bodyIdents;
            DCOMP._IEnvironment _88_bodyEnv;
            RAST._IExpr _out49;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out50;
            DCOMP._IEnvironment _out51;
            (this).GenStmts(_74_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out49, out _out50, out _out51);
            _86_bodyExpr = _out49;
            _87_bodyIdents = _out50;
            _88_bodyEnv = _out51;
            readIdents = _87_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), (_78_loopBegin).Then(_86_bodyExpr))));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_JumpTailCallStart) {
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Call) {
          DAST._IExpression _89_on = _source0.dtor_on;
          DAST._ICallName _90_name = _source0.dtor_callName;
          Dafny.ISequence<DAST._IType> _91_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _92_args = _source0.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _93_maybeOutVars = _source0.dtor_outs;
          {
            Dafny.ISequence<RAST._IExpr> _94_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _95_recIdents;
            Dafny.ISequence<RAST._IType> _96_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _97_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
            Dafny.ISequence<RAST._IType> _out54;
            Std.Wrappers._IOption<DAST._IResolvedType> _out55;
            (this).GenArgs(selfIdent, _90_name, _91_typeArgs, _92_args, env, out _out52, out _out53, out _out54, out _out55);
            _94_argExprs = _out52;
            _95_recIdents = _out53;
            _96_typeExprs = _out54;
            _97_fullNameQualifier = _out55;
            readIdents = _95_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source2 = _97_fullNameQualifier;
            {
              if (_source2.is_Some) {
                DAST._IResolvedType value0 = _source2.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _98_path = value0.dtor_path;
                Dafny.ISequence<DAST._IType> _99_onTypeArgs = value0.dtor_typeArgs;
                DAST._IResolvedTypeBase _100_base = value0.dtor_kind;
                RAST._IExpr _101_fullPath;
                RAST._IExpr _out56;
                _out56 = DCOMP.COMP.GenPathExpr(_98_path, true);
                _101_fullPath = _out56;
                Dafny.ISequence<RAST._IType> _102_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out57;
                _out57 = (this).GenTypeArgs(_99_onTypeArgs, DCOMP.GenTypeContext.@default());
                _102_onTypeExprs = _out57;
                RAST._IExpr _103_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _104_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _105_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_100_base).is_Trait) || ((_100_base).is_Class)) {
                  RAST._IExpr _out58;
                  DCOMP._IOwnership _out59;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
                  (this).GenExpr(_89_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out58, out _out59, out _out60);
                  _103_onExpr = _out58;
                  _104_recOwnership = _out59;
                  _105_recIdents = _out60;
                  _103_onExpr = ((this).modify__macro).Apply1(_103_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _105_recIdents);
                } else {
                  RAST._IExpr _out61;
                  DCOMP._IOwnership _out62;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out63;
                  (this).GenExpr(_89_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out61, out _out62, out _out63);
                  _103_onExpr = _out61;
                  _104_recOwnership = _out62;
                  _105_recIdents = _out63;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _105_recIdents);
                }
                generated = ((((_101_fullPath).ApplyType(_102_onTypeExprs)).FSel(DCOMP.__default.escapeName((_90_name).dtor_name))).ApplyType(_96_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_103_onExpr), _94_argExprs));
                goto after_match2;
              }
            }
            {
              RAST._IExpr _106_onExpr;
              DCOMP._IOwnership _107___v96;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _108_enclosingIdents;
              RAST._IExpr _out64;
              DCOMP._IOwnership _out65;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
              (this).GenExpr(_89_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out64, out _out65, out _out66);
              _106_onExpr = _out64;
              _107___v96 = _out65;
              _108_enclosingIdents = _out66;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _108_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _109_renderedName;
              _109_renderedName = (this).GetMethodName(_89_on, _90_name);
              DAST._IExpression _source3 = _89_on;
              {
                bool disjunctiveMatch0 = false;
                if (_source3.is_Companion) {
                  disjunctiveMatch0 = true;
                }
                if (_source3.is_ExternCompanion) {
                  disjunctiveMatch0 = true;
                }
                if (disjunctiveMatch0) {
                  {
                    _106_onExpr = (_106_onExpr).FSel(_109_renderedName);
                  }
                  goto after_match3;
                }
              }
              {
                {
                  if (!object.Equals(_106_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source4 = _90_name;
                    {
                      if (_source4.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source4.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _110_tpe = onType0.dtor_value;
                          RAST._IType _111_typ;
                          RAST._IType _out67;
                          _out67 = (this).GenType(_110_tpe, DCOMP.GenTypeContext.@default());
                          _111_typ = _out67;
                          if (((_111_typ).IsObjectOrPointer()) && (!object.Equals(_106_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _106_onExpr = ((this).modify__macro).Apply1(_106_onExpr);
                          }
                          goto after_match4;
                        }
                      }
                    }
                    {
                    }
                  after_match4: ;
                  }
                  _106_onExpr = (_106_onExpr).Sel(_109_renderedName);
                }
              }
            after_match3: ;
              generated = ((_106_onExpr).ApplyType(_96_typeExprs)).Apply(_94_argExprs);
            }
          after_match2: ;
            if (((_93_maybeOutVars).is_Some) && ((new BigInteger(((_93_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _112_outVar;
              _112_outVar = DCOMP.__default.escapeVar(((_93_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if (!((env).CanReadWithoutClone(_112_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_112_outVar, generated);
            } else if (((_93_maybeOutVars).is_None) || ((new BigInteger(((_93_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _113_tmpVar;
              _113_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _114_tmpId;
              _114_tmpId = RAST.Expr.create_Identifier(_113_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _113_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _115_outVars;
              _115_outVars = (_93_maybeOutVars).dtor_value;
              BigInteger _hi2 = new BigInteger((_115_outVars).Count);
              for (BigInteger _116_outI = BigInteger.Zero; _116_outI < _hi2; _116_outI++) {
                Dafny.ISequence<Dafny.Rune> _117_outVar;
                _117_outVar = DCOMP.__default.escapeVar((_115_outVars).Select(_116_outI));
                RAST._IExpr _118_rhs;
                _118_rhs = (_114_tmpId).Sel(Std.Strings.__default.OfNat(_116_outI));
                if (!((env).CanReadWithoutClone(_117_outVar))) {
                  _118_rhs = RAST.__default.MaybePlacebo(_118_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_117_outVar, _118_rhs));
              }
            }
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Return) {
          DAST._IExpression _119_exprDafny = _source0.dtor_expr;
          {
            RAST._IExpr _120_expr;
            DCOMP._IOwnership _121___v106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _122_recIdents;
            RAST._IExpr _out68;
            DCOMP._IOwnership _out69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out70;
            (this).GenExpr(_119_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out68, out _out69, out _out70);
            _120_expr = _out68;
            _121___v106 = _out69;
            _122_recIdents = _out70;
            readIdents = _122_recIdents;
            if (isLast) {
              generated = _120_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_120_expr));
            }
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_EarlyReturn) {
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source5 = earlyReturn;
            {
              if (_source5.is_None) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
                goto after_match5;
              }
            }
            {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _123_rustIdents = _source5.dtor_value;
              Dafny.ISequence<RAST._IExpr> _124_tupleArgs;
              _124_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi3 = new BigInteger((_123_rustIdents).Count);
              for (BigInteger _125_i = BigInteger.Zero; _125_i < _hi3; _125_i++) {
                RAST._IExpr _126_rIdent;
                DCOMP._IOwnership _127___v107;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _128___v108;
                RAST._IExpr _out71;
                DCOMP._IOwnership _out72;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out73;
                (this).GenIdent((_123_rustIdents).Select(_125_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out71, out _out72, out _out73);
                _126_rIdent = _out71;
                _127___v107 = _out72;
                _128___v108 = _out73;
                _124_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_124_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_126_rIdent));
              }
              if ((new BigInteger((_124_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_124_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_124_tupleArgs)));
              }
            }
          after_match5: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Halt) {
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        DAST._IExpression _129_e = _source0.dtor_Print_a0;
        {
          RAST._IExpr _130_printedExpr;
          DCOMP._IOwnership _131_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _132_recIdents;
          RAST._IExpr _out74;
          DCOMP._IOwnership _out75;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out76;
          (this).GenExpr(_129_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out74, out _out75, out _out76);
          _130_printedExpr = _out74;
          _131_recOwnership = _out75;
          _132_recIdents = _out76;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).AsExpr()).Apply1(_130_printedExpr)));
          readIdents = _132_recIdents;
          newEnv = env;
        }
      }
    after_match0: ;
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeRangeToRustType(DAST._INewtypeRange range) {
      DAST._INewtypeRange _source0 = range;
      {
        if (_source0.is_NoRange) {
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      {
        if (_source0.is_U8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      {
        if (_source0.is_U16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      {
        if (_source0.is_U32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      {
        if (_source0.is_U64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      {
        if (_source0.is_U128) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      {
        if (_source0.is_I8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      {
        if (_source0.is_I16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      {
        if (_source0.is_I32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      {
        if (_source0.is_I64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      {
        if (_source0.is_I128) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public void FromOwned(RAST._IExpr r, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        @out = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
        @out = r;
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
        @out = RAST.__default.Borrow(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        RAST._IExpr _out0;
        _out0 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Conversion from Borrowed or BorrowedMut to BorrowedMut"), r);
        @out = _out0;
        @out = ((this).modify__macro).Apply1(@out);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      }
    }
    public void FromOwnership(RAST._IExpr r, DCOMP._IOwnership ownership, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      if (object.Equals(ownership, expectedOwnership)) {
        @out = r;
        resultingOwnership = expectedOwnership;
        return ;
      }
      if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwned())) {
        RAST._IExpr _out0;
        DCOMP._IOwnership _out1;
        (this).FromOwned(r, expectedOwnership, out _out0, out _out1);
        @out = _out0;
        resultingOwnership = _out1;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out2;
        DCOMP._IOwnership _out3;
        (this).FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out2, out _out3);
        @out = _out2;
        resultingOwnership = _out3;
      } else if ((object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowedMut()))) {
        if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          @out = (r).Clone();
        } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
          @out = RAST.__default.BoxNew((r).Clone());
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
    public void GenExprLiteral(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source0 = e;
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h170 = _source0.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _0_b = _h170.dtor_BoolLiteral_a0;
            {
              RAST._IExpr _out0;
              DCOMP._IOwnership _out1;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_0_b), expectedOwnership, out _out0, out _out1);
              r = _out0;
              resultingOwnership = _out1;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h171 = _source0.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _2_t = _h171.dtor_IntLiteral_a1;
            {
              DAST._IType _source1 = _2_t;
              {
                if (_source1.is_Primitive) {
                  DAST._IPrimitive _h70 = _source1.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    {
                      if ((new BigInteger((_1_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralInt(_1_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1_i, true, false));
                      }
                    }
                    goto after_match1;
                  }
                }
              }
              {
                DAST._IType _3_o = _source1;
                {
                  RAST._IType _4_genType;
                  RAST._IType _out2;
                  _out2 = (this).GenType(_3_o, DCOMP.GenTypeContext.@default());
                  _4_genType = _out2;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_LiteralInt(_1_i), _4_genType);
                }
              }
            after_match1: ;
              RAST._IExpr _out3;
              DCOMP._IOwnership _out4;
              (this).FromOwned(r, expectedOwnership, out _out3, out _out4);
              r = _out3;
              resultingOwnership = _out4;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h172 = _source0.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _5_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _6_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _7_t = _h172.dtor_DecLiteral_a2;
            {
              DAST._IType _source2 = _7_t;
              {
                if (_source2.is_Primitive) {
                  DAST._IPrimitive _h71 = _source2.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    {
                      r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigInt"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("parse_bytes"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(_5_n, true, false), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("10"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0(), ((((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigInt"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("parse_bytes"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(_6_d, true, false), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("10"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0()));
                    }
                    goto after_match2;
                  }
                }
              }
              {
                DAST._IType _8_o = _source2;
                {
                  RAST._IType _9_genType;
                  RAST._IType _out5;
                  _out5 = (this).GenType(_8_o, DCOMP.GenTypeContext.@default());
                  _9_genType = _out5;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"), (RAST.Expr.create_LiteralInt(_5_n)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (RAST.Expr.create_LiteralInt(_6_d)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat()), _9_genType);
                }
              }
            after_match2: ;
              RAST._IExpr _out6;
              DCOMP._IOwnership _out7;
              (this).FromOwned(r, expectedOwnership, out _out6, out _out7);
              r = _out6;
              resultingOwnership = _out7;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h173 = _source0.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _10_l = _h173.dtor_StringLiteral_a0;
            bool _11_verbatim = _h173.dtor_verbatim;
            {
              r = (((RAST.__default.dafny__runtime).MSel((this).string__of)).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_10_l, false, _11_verbatim));
              RAST._IExpr _out8;
              DCOMP._IOwnership _out9;
              (this).FromOwned(r, expectedOwnership, out _out8, out _out9);
              r = _out8;
              resultingOwnership = _out9;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h174 = _source0.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _12_c = _h174.dtor_CharLiteralUTF16_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_12_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
              RAST._IExpr _out10;
              DCOMP._IOwnership _out11;
              (this).FromOwned(r, expectedOwnership, out _out10, out _out11);
              r = _out10;
              resultingOwnership = _out11;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h175 = _source0.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _13_c = _h175.dtor_CharLiteral_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_13_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0();
              }
              r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
              RAST._IExpr _out12;
              DCOMP._IOwnership _out13;
              (this).FromOwned(r, expectedOwnership, out _out12, out _out13);
              r = _out12;
              resultingOwnership = _out13;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        DAST._ILiteral _h176 = _source0.dtor_Literal_a0;
        DAST._IType _14_tpe = _h176.dtor_Null_a0;
        {
          RAST._IType _15_tpeGen;
          RAST._IType _out14;
          _out14 = (this).GenType(_14_tpe, DCOMP.GenTypeContext.@default());
          _15_tpeGen = _out14;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null_mut"));
          } else {
            r = RAST.Expr.create_TypeAscription((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _15_tpeGen);
          }
          RAST._IExpr _out15;
          DCOMP._IOwnership _out16;
          (this).FromOwned(r, expectedOwnership, out _out15, out _out16);
          r = _out15;
          resultingOwnership = _out16;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      }
    after_match0: ;
    }
    public void GenExprBinary(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IBinOp _0_op = _let_tmp_rhs0.dtor_op;
      DAST._IExpression _1_lExpr = _let_tmp_rhs0.dtor_left;
      DAST._IExpression _2_rExpr = _let_tmp_rhs0.dtor_right;
      DAST.Format._IBinaryOpFormat _3_format = _let_tmp_rhs0.dtor_format2;
      bool _4_becomesLeftCallsRight;
      DAST._IBinOp _source0 = _0_op;
      {
        bool disjunctiveMatch0 = false;
        if (_source0.is_SetMerge) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetSubtraction) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetIntersection) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetDisjoint) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MapMerge) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MapSubtraction) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetMerge) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetSubtraction) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetIntersection) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetDisjoint) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_Concat) {
          disjunctiveMatch0 = true;
        }
        if (disjunctiveMatch0) {
          _4_becomesLeftCallsRight = true;
          goto after_match0;
        }
      }
      {
        _4_becomesLeftCallsRight = false;
      }
    after_match0: ;
      bool _5_becomesRightCallsLeft;
      DAST._IBinOp _source1 = _0_op;
      {
        if (_source1.is_In) {
          _5_becomesRightCallsLeft = true;
          goto after_match1;
        }
      }
      {
        _5_becomesRightCallsLeft = false;
      }
    after_match1: ;
      bool _6_becomesCallLeftRight;
      DAST._IBinOp _source2 = _0_op;
      {
        if (_source2.is_Eq) {
          bool referential0 = _source2.dtor_referential;
          if ((referential0) == (true)) {
            _6_becomesCallLeftRight = false;
            goto after_match2;
          }
        }
      }
      {
        if (_source2.is_SetMerge) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_SetSubtraction) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_SetIntersection) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_SetDisjoint) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MapMerge) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MapSubtraction) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MultisetMerge) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MultisetSubtraction) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MultisetIntersection) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_MultisetDisjoint) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        if (_source2.is_Concat) {
          _6_becomesCallLeftRight = true;
          goto after_match2;
        }
      }
      {
        _6_becomesCallLeftRight = false;
      }
    after_match2: ;
      DCOMP._IOwnership _7_expectedLeftOwnership;
      if (_4_becomesLeftCallsRight) {
        _7_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else if ((_5_becomesRightCallsLeft) || (_6_becomesCallLeftRight)) {
        _7_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        _7_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      DCOMP._IOwnership _8_expectedRightOwnership;
      if ((_4_becomesLeftCallsRight) || (_6_becomesCallLeftRight)) {
        _8_expectedRightOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else if (_5_becomesRightCallsLeft) {
        _8_expectedRightOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else {
        _8_expectedRightOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      RAST._IExpr _9_left;
      DCOMP._IOwnership _10___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _11_recIdentsL;
      RAST._IExpr _out0;
      DCOMP._IOwnership _out1;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
      (this).GenExpr(_1_lExpr, selfIdent, env, _7_expectedLeftOwnership, out _out0, out _out1, out _out2);
      _9_left = _out0;
      _10___v113 = _out1;
      _11_recIdentsL = _out2;
      RAST._IExpr _12_right;
      DCOMP._IOwnership _13___v114;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14_recIdentsR;
      RAST._IExpr _out3;
      DCOMP._IOwnership _out4;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
      (this).GenExpr(_2_rExpr, selfIdent, env, _8_expectedRightOwnership, out _out3, out _out4, out _out5);
      _12_right = _out3;
      _13___v114 = _out4;
      _14_recIdentsR = _out5;
      DAST._IBinOp _source3 = _0_op;
      {
        if (_source3.is_In) {
          {
            r = ((_12_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_9_left);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_SeqProperPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _9_left, _12_right, _3_format);
          goto after_match3;
        }
      }
      {
        if (_source3.is_SeqPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _9_left, _12_right, _3_format);
          goto after_match3;
        }
      }
      {
        if (_source3.is_SetMerge) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_SetSubtraction) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_SetIntersection) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_Subset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _9_left, _12_right, _3_format);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_ProperSubset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _9_left, _12_right, _3_format);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_SetDisjoint) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MapMerge) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MapSubtraction) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MultisetMerge) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MultisetSubtraction) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MultisetIntersection) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_Submultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _9_left, _12_right, _3_format);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_ProperSubmultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _9_left, _12_right, _3_format);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_MultisetDisjoint) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        if (_source3.is_Concat) {
          {
            r = ((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_12_right);
          }
          goto after_match3;
        }
      }
      {
        {
          if ((DCOMP.COMP.OpTable).Contains(_0_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_0_op), _9_left, _12_right, _3_format);
          } else {
            DAST._IBinOp _source4 = _0_op;
            {
              if (_source4.is_Eq) {
                bool _15_referential = _source4.dtor_referential;
                {
                  if (_15_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      RAST._IExpr _out6;
                      _out6 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"), (this).InitEmptyExpr());
                      r = _out6;
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _9_left, _12_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_2_rExpr).is_SeqValue) && ((new BigInteger(((_2_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_9_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply0(), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1_lExpr).is_SeqValue) && ((new BigInteger(((_1_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_12_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply0(), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _9_left, _12_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
                goto after_match4;
              }
            }
            {
              if (_source4.is_EuclidianDiv) {
                {
                  r = (((RAST.__default.dafny__runtime).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_9_left, _12_right));
                }
                goto after_match4;
              }
            }
            {
              if (_source4.is_EuclidianMod) {
                {
                  r = (((RAST.__default.dafny__runtime).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_9_left, _12_right));
                }
                goto after_match4;
              }
            }
            {
              Dafny.ISequence<Dafny.Rune> _16_op = _source4.dtor_Passthrough_a0;
              {
                r = RAST.Expr.create_BinaryOp(_16_op, _9_left, _12_right, _3_format);
              }
            }
          after_match4: ;
          }
        }
      }
    after_match3: ;
      RAST._IExpr _out7;
      DCOMP._IOwnership _out8;
      (this).FromOwned(r, expectedOwnership, out _out7, out _out8);
      r = _out7;
      resultingOwnership = _out8;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_11_recIdentsL, _14_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IExpression _0_expr = _let_tmp_rhs0.dtor_value;
      DAST._IType _1_fromTpe = _let_tmp_rhs0.dtor_from;
      DAST._IType _2_toTpe = _let_tmp_rhs0.dtor_typ;
      DAST._IType _let_tmp_rhs1 = _2_toTpe;
      DAST._IResolvedType _let_tmp_rhs2 = _let_tmp_rhs1.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3_path = _let_tmp_rhs2.dtor_path;
      Dafny.ISequence<DAST._IType> _4_typeArgs = _let_tmp_rhs2.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs3 = _let_tmp_rhs2.dtor_kind;
      DAST._IType _5_b = _let_tmp_rhs3.dtor_baseType;
      DAST._INewtypeRange _6_range = _let_tmp_rhs3.dtor_range;
      bool _7_erase = _let_tmp_rhs3.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _8___v116 = _let_tmp_rhs2.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _9___v117 = _let_tmp_rhs2.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _10___v118 = _let_tmp_rhs2.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _11_nativeToType;
      _11_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_6_range);
      if (object.Equals(_1_fromTpe, _5_b)) {
        RAST._IExpr _12_recursiveGen;
        DCOMP._IOwnership _13_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14_recIdents;
        RAST._IExpr _out0;
        DCOMP._IOwnership _out1;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
        (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out0, out _out1, out _out2);
        _12_recursiveGen = _out0;
        _13_recOwned = _out1;
        _14_recIdents = _out2;
        readIdents = _14_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source0 = _11_nativeToType;
        {
          if (_source0.is_Some) {
            RAST._IType _15_v = _source0.dtor_value;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_12_recursiveGen, RAST.Expr.create_ExprFromType(_15_v)));
            RAST._IExpr _out3;
            DCOMP._IOwnership _out4;
            (this).FromOwned(r, expectedOwnership, out _out3, out _out4);
            r = _out3;
            resultingOwnership = _out4;
            goto after_match0;
          }
        }
        {
          if (_7_erase) {
            r = _12_recursiveGen;
          } else {
            RAST._IType _16_rhsType;
            RAST._IType _out5;
            _out5 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.@default());
            _16_rhsType = _out5;
            r = (RAST.Expr.create_ExprFromType(_16_rhsType)).Apply1(_12_recursiveGen);
          }
          RAST._IExpr _out6;
          DCOMP._IOwnership _out7;
          (this).FromOwnership(r, _13_recOwned, expectedOwnership, out _out6, out _out7);
          r = _out6;
          resultingOwnership = _out7;
        }
      after_match0: ;
      } else {
        if ((_11_nativeToType).is_Some) {
          DAST._IType _source1 = _1_fromTpe;
          {
            if (_source1.is_UserDefined) {
              DAST._IResolvedType resolved0 = _source1.dtor_resolved;
              DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
              if (kind0.is_Newtype) {
                DAST._IType _17_b0 = kind0.dtor_baseType;
                DAST._INewtypeRange _18_range0 = kind0.dtor_range;
                bool _19_erase0 = kind0.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _20_attributes0 = resolved0.dtor_attributes;
                {
                  Std.Wrappers._IOption<RAST._IType> _21_nativeFromType;
                  _21_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_18_range0);
                  if ((_21_nativeFromType).is_Some) {
                    RAST._IExpr _22_recursiveGen;
                    DCOMP._IOwnership _23_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _24_recIdents;
                    RAST._IExpr _out8;
                    DCOMP._IOwnership _out9;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out10;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out8, out _out9, out _out10);
                    _22_recursiveGen = _out8;
                    _23_recOwned = _out9;
                    _24_recIdents = _out10;
                    RAST._IExpr _out11;
                    DCOMP._IOwnership _out12;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_22_recursiveGen, (_11_nativeToType).dtor_value), _23_recOwned, expectedOwnership, out _out11, out _out12);
                    r = _out11;
                    resultingOwnership = _out12;
                    readIdents = _24_recIdents;
                    return ;
                  }
                }
                goto after_match1;
              }
            }
          }
          {
          }
        after_match1: ;
          if (object.Equals(_1_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _25_recursiveGen;
            DCOMP._IOwnership _26_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _27_recIdents;
            RAST._IExpr _out13;
            DCOMP._IOwnership _out14;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out15;
            (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out13, out _out14, out _out15);
            _25_recursiveGen = _out13;
            _26_recOwned = _out14;
            _27_recIdents = _out15;
            RAST._IExpr _out16;
            DCOMP._IOwnership _out17;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_25_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_11_nativeToType).dtor_value), _26_recOwned, expectedOwnership, out _out16, out _out17);
            r = _out16;
            resultingOwnership = _out17;
            readIdents = _27_recIdents;
            return ;
          }
        }
        RAST._IExpr _out18;
        DCOMP._IOwnership _out19;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out20;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_0_expr, _1_fromTpe, _5_b), _5_b, _2_toTpe), selfIdent, env, expectedOwnership, out _out18, out _out19, out _out20);
        r = _out18;
        resultingOwnership = _out19;
        readIdents = _out20;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IExpression _0_expr = _let_tmp_rhs0.dtor_value;
      DAST._IType _1_fromTpe = _let_tmp_rhs0.dtor_from;
      DAST._IType _2_toTpe = _let_tmp_rhs0.dtor_typ;
      DAST._IType _let_tmp_rhs1 = _1_fromTpe;
      DAST._IResolvedType _let_tmp_rhs2 = _let_tmp_rhs1.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3___v124 = _let_tmp_rhs2.dtor_path;
      Dafny.ISequence<DAST._IType> _4___v125 = _let_tmp_rhs2.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs3 = _let_tmp_rhs2.dtor_kind;
      DAST._IType _5_b = _let_tmp_rhs3.dtor_baseType;
      DAST._INewtypeRange _6_range = _let_tmp_rhs3.dtor_range;
      bool _7_erase = _let_tmp_rhs3.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _8_attributes = _let_tmp_rhs2.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _9___v126 = _let_tmp_rhs2.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _10___v127 = _let_tmp_rhs2.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _11_nativeFromType;
      _11_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_6_range);
      if (object.Equals(_5_b, _2_toTpe)) {
        RAST._IExpr _12_recursiveGen;
        DCOMP._IOwnership _13_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14_recIdents;
        RAST._IExpr _out0;
        DCOMP._IOwnership _out1;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
        (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out0, out _out1, out _out2);
        _12_recursiveGen = _out0;
        _13_recOwned = _out1;
        _14_recIdents = _out2;
        readIdents = _14_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source0 = _11_nativeFromType;
        {
          if (_source0.is_Some) {
            RAST._IType _15_v = _source0.dtor_value;
            RAST._IType _16_toTpeRust;
            RAST._IType _out3;
            _out3 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.@default());
            _16_toTpeRust = _out3;
            r = ((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_16_toTpeRust))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_12_recursiveGen));
            RAST._IExpr _out4;
            DCOMP._IOwnership _out5;
            (this).FromOwned(r, expectedOwnership, out _out4, out _out5);
            r = _out4;
            resultingOwnership = _out5;
            goto after_match0;
          }
        }
        {
          if (_7_erase) {
            r = _12_recursiveGen;
          } else {
            r = (_12_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out6;
          DCOMP._IOwnership _out7;
          (this).FromOwnership(r, _13_recOwned, expectedOwnership, out _out6, out _out7);
          r = _out6;
          resultingOwnership = _out7;
        }
      after_match0: ;
      } else {
        if ((_11_nativeFromType).is_Some) {
          if (object.Equals(_2_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _17_recursiveGen;
            DCOMP._IOwnership _18_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _19_recIdents;
            RAST._IExpr _out8;
            DCOMP._IOwnership _out9;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out10;
            (this).GenExpr(_0_expr, selfIdent, env, expectedOwnership, out _out8, out _out9, out _out10);
            _17_recursiveGen = _out8;
            _18_recOwned = _out9;
            _19_recIdents = _out10;
            RAST._IExpr _out11;
            DCOMP._IOwnership _out12;
            (this).FromOwnership((((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(RAST.Expr.create_TypeAscription(_17_recursiveGen, (this).DafnyCharUnderlying)), _18_recOwned, expectedOwnership, out _out11, out _out12);
            r = _out11;
            resultingOwnership = _out12;
            readIdents = _19_recIdents;
            return ;
          }
        }
        RAST._IExpr _out13;
        DCOMP._IOwnership _out14;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out15;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_0_expr, _1_fromTpe, _5_b), _5_b, _2_toTpe), selfIdent, env, expectedOwnership, out _out13, out _out14, out _out15);
        r = _out13;
        resultingOwnership = _out14;
        readIdents = _out15;
      }
    }
    public bool IsBuiltinCollection(DAST._IType typ) {
      return ((((typ).is_Seq) || ((typ).is_Set)) || ((typ).is_Map)) || ((typ).is_Multiset);
    }
    public DAST._IType GetBuiltinCollectionElement(DAST._IType typ) {
      if ((typ).is_Map) {
        return (typ).dtor_value;
      } else {
        return (typ).dtor_element;
      }
    }
    public bool SameTypesButDifferentTypeParameters(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe)
    {
      return (((((((fromTpe).is_TypeApp) && ((toTpe).is_TypeApp)) && (object.Equals((fromTpe).dtor_baseName, (toTpe).dtor_baseName))) && ((fromType).is_UserDefined)) && ((toType).is_UserDefined)) && ((this).IsSameResolvedTypeAnyArgs((fromType).dtor_resolved, (toType).dtor_resolved))) && ((((new BigInteger((((fromType).dtor_resolved).dtor_typeArgs).Count)) == (new BigInteger((((toType).dtor_resolved).dtor_typeArgs).Count))) && ((new BigInteger((((toType).dtor_resolved).dtor_typeArgs).Count)) == (new BigInteger(((fromTpe).dtor_arguments).Count)))) && ((new BigInteger(((fromTpe).dtor_arguments).Count)) == (new BigInteger(((toTpe).dtor_arguments).Count))));
    }
    public Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> SeqResultToResultSeq<__T, __E>(Dafny.ISequence<Std.Wrappers._IResult<__T, __E>> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.FromElements());
      } else {
        Std.Wrappers._IResult<__T, __E> _0_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_0_valueOrError0).IsFailure()) {
          return (_0_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1_head = (_0_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _2_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_2_valueOrError1).IsFailure()) {
            return (_2_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _3_tail = (_2_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1_head), _3_tail));
          }
        }
      }
    }
    public Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> UpcastConversionLambda(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> typeParams)
    {
      var _pat_let_tv0 = fromType;
      var _pat_let_tv1 = fromTpe;
      var _pat_let_tv2 = toType;
      var _pat_let_tv3 = toTpe;
      var _pat_let_tv4 = typeParams;
      if (object.Equals(fromTpe, toTpe)) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_id"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(fromTpe))).Apply0());
      } else if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        if (!(((toTpe).ObjectOrPointerUnderlying()).is_DynType)) {
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
        } else {
          RAST._IType _0_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel((this).upcast)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_0_fromTpeUnderlying, _1_toTpeUnderlying))).Apply0());
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _2_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_2_valueOrError0).IsFailure()) {
          return (_2_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _3_lambda = (_2_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_3_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).AsExpr()).Apply1(_3_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Dafny.ISequence<BigInteger> _4_indices = ((((fromType).is_UserDefined) && ((((fromType).dtor_resolved).dtor_kind).is_Datatype)) ? (Std.Collections.Seq.__default.Filter<BigInteger>(Dafny.Helpers.Id<Func<RAST._IType, DAST._IType, Func<BigInteger, bool>>>((_5_fromTpe, _6_fromType) => ((System.Func<BigInteger, bool>)((_7_i) => {
          return ((((_7_i).Sign != -1) && ((_7_i) < (new BigInteger(((_5_fromTpe).dtor_arguments).Count)))) ? (!(((_7_i).Sign != -1) && ((_7_i) < (new BigInteger(((((_6_fromType).dtor_resolved).dtor_kind).dtor_variances).Count)))) || (!((((((_6_fromType).dtor_resolved).dtor_kind).dtor_variances).Select(_7_i)).is_Nonvariant))) : (false));
        })))(fromTpe, fromType), ((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim14 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr14 = new BigInteger[Dafny.Helpers.ToIntChecked(dim14, "array size exceeds memory limit")];
          for (int i14 = 0; i14 < dim14; i14++) {
            var _8_i = (BigInteger) i14;
            arr14[(int)(_8_i)] = _8_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr14);
        }))())) : (((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim15 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr15 = new BigInteger[Dafny.Helpers.ToIntChecked(dim15, "array size exceeds memory limit")];
          for (int i15 = 0; i15 < dim15; i15++) {
            var _9_i = (BigInteger) i15;
            arr15[(int)(_9_i)] = _9_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr15);
        }))()));
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _10_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim16 = new BigInteger((_4_indices).Count);
          var arr16 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim16, "array size exceeds memory limit")];
          for (int i16 = 0; i16 < dim16; i16++) {
            var _11_j = (BigInteger) i16;
            arr16[(int)(_11_j)] = Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>((_4_indices).Select(_11_j), _pat_let22_0 => Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>(_pat_let22_0, _12_i => (this).UpcastConversionLambda((((_pat_let_tv0).dtor_resolved).dtor_typeArgs).Select(_12_i), ((_pat_let_tv1).dtor_arguments).Select(_12_i), (((_pat_let_tv2).dtor_resolved).dtor_typeArgs).Select(_12_i), ((_pat_let_tv3).dtor_arguments).Select(_12_i), _pat_let_tv4)));
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr16);
        }))());
        if ((_10_valueOrError1).IsFailure()) {
          return (_10_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _13_lambdas = (_10_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim17 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr17 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim17, "array size exceeds memory limit")];
  for (int i17 = 0; i17 < dim17; i17++) {
    var _14_i = (BigInteger) i17;
    arr17[(int)(_14_i)] = ((fromTpe).dtor_arguments).Select(_14_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr17);
}))())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_13_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _15_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _16_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _17_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _18_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _19_valueOrError2 = (this).UpcastConversionLambda(_17_newFromType, _15_newFromTpe, _18_newToType, _16_newToTpe, typeParams);
        if ((_19_valueOrError2).IsFailure()) {
          return (_19_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _20_coerceArg = (_19_valueOrError2).Extract();
          RAST._IPath _21_collectionType = (RAST.__default.dafny__runtime).MSel(((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name);
          RAST._IExpr _22_baseType = (((((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? (((_21_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _15_newFromTpe))) : (((_21_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_15_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_22_baseType).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_20_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _23_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_23_valueOrError3).IsFailure()) {
          return (_23_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _24_lambda = (_23_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_24_lambda));
        }
      } else {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
      }
    }
    public bool IsDowncastConversion(RAST._IType fromTpe, RAST._IType toTpe)
    {
      if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        return (((fromTpe).ObjectOrPointerUnderlying()).is_DynType) && (!(((toTpe).ObjectOrPointerUnderlying()).is_DynType));
      } else {
        return false;
      }
    }
    public void GenExprConvertOther(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IExpression _0_expr = _let_tmp_rhs0.dtor_value;
      DAST._IType _1_fromTpe = _let_tmp_rhs0.dtor_from;
      DAST._IType _2_toTpe = _let_tmp_rhs0.dtor_typ;
      RAST._IType _3_fromTpeGen;
      RAST._IType _out0;
      _out0 = (this).GenType(_1_fromTpe, DCOMP.GenTypeContext.@default());
      _3_fromTpeGen = _out0;
      RAST._IType _4_toTpeGen;
      RAST._IType _out1;
      _out1 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.@default());
      _4_toTpeGen = _out1;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _5_upcastConverter;
      _5_upcastConverter = (this).UpcastConversionLambda(_1_fromTpe, _3_fromTpeGen, _2_toTpe, _4_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_5_upcastConverter).is_Success) {
        RAST._IExpr _6_conversionLambda;
        _6_conversionLambda = (_5_upcastConverter).dtor_value;
        RAST._IExpr _7_recursiveGen;
        DCOMP._IOwnership _8_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _9_recIdents;
        RAST._IExpr _out2;
        DCOMP._IOwnership _out3;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out4;
        (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out2, out _out3, out _out4);
        _7_recursiveGen = _out2;
        _8_recOwned = _out3;
        _9_recIdents = _out4;
        readIdents = _9_recIdents;
        r = (_6_conversionLambda).Apply1(_7_recursiveGen);
        RAST._IExpr _out5;
        DCOMP._IOwnership _out6;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out5, out _out6);
        r = _out5;
        resultingOwnership = _out6;
      } else if ((this).IsDowncastConversion(_3_fromTpeGen, _4_toTpeGen)) {
        RAST._IExpr _10_recursiveGen;
        DCOMP._IOwnership _11_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _12_recIdents;
        RAST._IExpr _out7;
        DCOMP._IOwnership _out8;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out9;
        (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out7, out _out8, out _out9);
        _10_recursiveGen = _out7;
        _11_recOwned = _out8;
        _12_recIdents = _out9;
        readIdents = _12_recIdents;
        _4_toTpeGen = (_4_toTpeGen).ObjectOrPointerUnderlying();
        r = (((RAST.__default.dafny__runtime).MSel((this).downcast)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_10_recursiveGen, RAST.Expr.create_ExprFromType(_4_toTpeGen)));
        RAST._IExpr _out10;
        DCOMP._IOwnership _out11;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out10, out _out11);
        r = _out10;
        resultingOwnership = _out11;
      } else {
        RAST._IExpr _13_recursiveGen;
        DCOMP._IOwnership _14_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _15_recIdents;
        RAST._IExpr _out12;
        DCOMP._IOwnership _out13;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out14;
        (this).GenExpr(_0_expr, selfIdent, env, expectedOwnership, out _out12, out _out13, out _out14);
        _13_recursiveGen = _out12;
        _14_recOwned = _out13;
        _15_recIdents = _out14;
        readIdents = _15_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs1 = _5_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs2 = _let_tmp_rhs1.dtor_error;
        DAST._IType _16_fromType = _let_tmp_rhs2.dtor__0;
        RAST._IType _17_fromTpeGen = _let_tmp_rhs2.dtor__1;
        DAST._IType _18_toType = _let_tmp_rhs2.dtor__2;
        RAST._IType _19_toTpeGen = _let_tmp_rhs2.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _20_m = _let_tmp_rhs2.dtor__4;
        RAST._IExpr _out15;
        _out15 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Coercion from "), (_17_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_19_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented")), _13_recursiveGen);
        r = _out15;
        RAST._IExpr _out16;
        DCOMP._IOwnership _out17;
        (this).FromOwnership(r, _14_recOwned, expectedOwnership, out _out16, out _out17);
        r = _out16;
        resultingOwnership = _out17;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IExpression _0_expr = _let_tmp_rhs0.dtor_value;
      DAST._IType _1_fromTpe = _let_tmp_rhs0.dtor_from;
      DAST._IType _2_toTpe = _let_tmp_rhs0.dtor_typ;
      if (object.Equals(_1_fromTpe, _2_toTpe)) {
        RAST._IExpr _3_recursiveGen;
        DCOMP._IOwnership _4_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5_recIdents;
        RAST._IExpr _out0;
        DCOMP._IOwnership _out1;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
        (this).GenExpr(_0_expr, selfIdent, env, expectedOwnership, out _out0, out _out1, out _out2);
        _3_recursiveGen = _out0;
        _4_recOwned = _out1;
        _5_recIdents = _out2;
        r = _3_recursiveGen;
        RAST._IExpr _out3;
        DCOMP._IOwnership _out4;
        (this).FromOwnership(r, _4_recOwned, expectedOwnership, out _out3, out _out4);
        r = _out3;
        resultingOwnership = _out4;
        readIdents = _5_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source0 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1_fromTpe, _2_toTpe);
        {
          DAST._IType _10 = _source0.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved0 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Newtype) {
              DAST._IType _6_b = kind0.dtor_baseType;
              DAST._INewtypeRange _7_range = kind0.dtor_range;
              bool _8_erase = kind0.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _9_attributes = resolved0.dtor_attributes;
              {
                RAST._IExpr _out5;
                DCOMP._IOwnership _out6;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out5, out _out6, out _out7);
                r = _out5;
                resultingOwnership = _out6;
                readIdents = _out7;
              }
              goto after_match0;
            }
          }
        }
        {
          DAST._IType _00 = _source0.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved1 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
            if (kind1.is_Newtype) {
              DAST._IType _10_b = kind1.dtor_baseType;
              DAST._INewtypeRange _11_range = kind1.dtor_range;
              bool _12_erase = kind1.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _13_attributes = resolved1.dtor_attributes;
              {
                RAST._IExpr _out8;
                DCOMP._IOwnership _out9;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out10;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out8, out _out9, out _out10);
                r = _out8;
                resultingOwnership = _out9;
                readIdents = _out10;
              }
              goto after_match0;
            }
          }
        }
        {
          DAST._IType _01 = _source0.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h70 = _01.dtor_Primitive_a0;
            if (_h70.is_Int) {
              DAST._IType _11 = _source0.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h71 = _11.dtor_Primitive_a0;
                if (_h71.is_Real) {
                  {
                    RAST._IExpr _14_recursiveGen;
                    DCOMP._IOwnership _15___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _16_recIdents;
                    RAST._IExpr _out11;
                    DCOMP._IOwnership _out12;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out13;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out11, out _out12, out _out13);
                    _14_recursiveGen = _out11;
                    _15___v138 = _out12;
                    _16_recIdents = _out13;
                    r = RAST.__default.RcNew(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_integer"))).Apply1(_14_recursiveGen));
                    RAST._IExpr _out14;
                    DCOMP._IOwnership _out15;
                    (this).FromOwned(r, expectedOwnership, out _out14, out _out15);
                    r = _out14;
                    resultingOwnership = _out15;
                    readIdents = _16_recIdents;
                  }
                  goto after_match0;
                }
              }
            }
          }
        }
        {
          DAST._IType _02 = _source0.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h72 = _02.dtor_Primitive_a0;
            if (_h72.is_Real) {
              DAST._IType _12 = _source0.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h73 = _12.dtor_Primitive_a0;
                if (_h73.is_Int) {
                  {
                    RAST._IExpr _17_recursiveGen;
                    DCOMP._IOwnership _18___v139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _19_recIdents;
                    RAST._IExpr _out16;
                    DCOMP._IOwnership _out17;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out18;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out16, out _out17, out _out18);
                    _17_recursiveGen = _out16;
                    _18___v139 = _out17;
                    _19_recIdents = _out18;
                    r = (((RAST.__default.dafny__runtime).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_rational_to_int"))).Apply1(_17_recursiveGen);
                    RAST._IExpr _out19;
                    DCOMP._IOwnership _out20;
                    (this).FromOwned(r, expectedOwnership, out _out19, out _out20);
                    r = _out19;
                    resultingOwnership = _out20;
                    readIdents = _19_recIdents;
                  }
                  goto after_match0;
                }
              }
            }
          }
        }
        {
          DAST._IType _03 = _source0.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h74 = _03.dtor_Primitive_a0;
            if (_h74.is_Int) {
              DAST._IType _13 = _source0.dtor__1;
              if (_13.is_Passthrough) {
                {
                  RAST._IType _20_rhsType;
                  RAST._IType _out21;
                  _out21 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.@default());
                  _20_rhsType = _out21;
                  RAST._IExpr _21_recursiveGen;
                  DCOMP._IOwnership _22___v141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _23_recIdents;
                  RAST._IExpr _out22;
                  DCOMP._IOwnership _out23;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out24;
                  (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out22, out _out23, out _out24);
                  _21_recursiveGen = _out22;
                  _22___v141 = _out23;
                  _23_recIdents = _out24;
                  r = ((((RAST.Expr.create_TraitCast(_20_rhsType, ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("NumCast"))).AsType())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(_21_recursiveGen)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0();
                  RAST._IExpr _out25;
                  DCOMP._IOwnership _out26;
                  (this).FromOwned(r, expectedOwnership, out _out25, out _out26);
                  r = _out25;
                  resultingOwnership = _out26;
                  readIdents = _23_recIdents;
                }
                goto after_match0;
              }
            }
          }
        }
        {
          DAST._IType _04 = _source0.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source0.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h75 = _14.dtor_Primitive_a0;
              if (_h75.is_Int) {
                {
                  RAST._IType _24_rhsType;
                  RAST._IType _out27;
                  _out27 = (this).GenType(_1_fromTpe, DCOMP.GenTypeContext.@default());
                  _24_rhsType = _out27;
                  RAST._IExpr _25_recursiveGen;
                  DCOMP._IOwnership _26___v143;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _27_recIdents;
                  RAST._IExpr _out28;
                  DCOMP._IOwnership _out29;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out30;
                  (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out28, out _out29, out _out30);
                  _25_recursiveGen = _out28;
                  _26___v143 = _out29;
                  _27_recIdents = _out30;
                  r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply1((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Rc"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply1(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigInt"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(_25_recursiveGen)));
                  RAST._IExpr _out31;
                  DCOMP._IOwnership _out32;
                  (this).FromOwned(r, expectedOwnership, out _out31, out _out32);
                  r = _out31;
                  resultingOwnership = _out32;
                  readIdents = _27_recIdents;
                }
                goto after_match0;
              }
            }
          }
        }
        {
          DAST._IType _05 = _source0.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h76 = _05.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _15 = _source0.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h77 = _15.dtor_Primitive_a0;
                if (_h77.is_Char) {
                  {
                    RAST._IType _28_rhsType;
                    RAST._IType _out33;
                    _out33 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.@default());
                    _28_rhsType = _out33;
                    RAST._IExpr _29_recursiveGen;
                    DCOMP._IOwnership _30___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _31_recIdents;
                    RAST._IExpr _out34;
                    DCOMP._IOwnership _out35;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out36;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out34, out _out35, out _out36);
                    _29_recursiveGen = _out34;
                    _30___v144 = _out35;
                    _31_recIdents = _out36;
                    RAST._IType _32_uType;
                    if ((this).UnicodeChars) {
                      _32_uType = RAST.Type.create_U32();
                    } else {
                      _32_uType = RAST.Type.create_U16();
                    }
                    r = RAST.Expr.create_TraitCast(_32_uType, ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("NumCast"))).AsType());
                    r = ((((r).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(_29_recursiveGen)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0();
                    if ((this).UnicodeChars) {
                      r = ((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(((r).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0());
                    }
                    r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
                    RAST._IExpr _out37;
                    DCOMP._IOwnership _out38;
                    (this).FromOwned(r, expectedOwnership, out _out37, out _out38);
                    r = _out37;
                    resultingOwnership = _out38;
                    readIdents = _31_recIdents;
                  }
                  goto after_match0;
                }
              }
            }
          }
        }
        {
          DAST._IType _06 = _source0.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h78 = _06.dtor_Primitive_a0;
            if (_h78.is_Char) {
              DAST._IType _16 = _source0.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h79 = _16.dtor_Primitive_a0;
                if (_h79.is_Int) {
                  {
                    RAST._IType _33_rhsType;
                    RAST._IType _out39;
                    _out39 = (this).GenType(_1_fromTpe, DCOMP.GenTypeContext.@default());
                    _33_rhsType = _out39;
                    RAST._IExpr _34_recursiveGen;
                    DCOMP._IOwnership _35___v145;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _36_recIdents;
                    RAST._IExpr _out40;
                    DCOMP._IOwnership _out41;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out42;
                    (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out40, out _out41, out _out42);
                    _34_recursiveGen = _out40;
                    _35___v145 = _out41;
                    _36_recIdents = _out42;
                    r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1((_34_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out43;
                    DCOMP._IOwnership _out44;
                    (this).FromOwned(r, expectedOwnership, out _out43, out _out44);
                    r = _out43;
                    resultingOwnership = _out44;
                    readIdents = _36_recIdents;
                  }
                  goto after_match0;
                }
              }
            }
          }
        }
        {
          DAST._IType _07 = _source0.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source0.dtor__1;
            if (_17.is_Passthrough) {
              {
                RAST._IExpr _37_recursiveGen;
                DCOMP._IOwnership _38___v148;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _39_recIdents;
                RAST._IExpr _out45;
                DCOMP._IOwnership _out46;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out47;
                (this).GenExpr(_0_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out45, out _out46, out _out47);
                _37_recursiveGen = _out45;
                _38___v148 = _out46;
                _39_recIdents = _out47;
                RAST._IType _40_toTpeGen;
                RAST._IType _out48;
                _out48 = (this).GenType(_2_toTpe, DCOMP.GenTypeContext.@default());
                _40_toTpeGen = _out48;
                r = RAST.Expr.create_TypeAscription(_37_recursiveGen, _40_toTpeGen);
                RAST._IExpr _out49;
                DCOMP._IOwnership _out50;
                (this).FromOwned(r, expectedOwnership, out _out49, out _out50);
                r = _out49;
                resultingOwnership = _out50;
                readIdents = _39_recIdents;
              }
              goto after_match0;
            }
          }
        }
        {
          {
            RAST._IExpr _out51;
            DCOMP._IOwnership _out52;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out53;
            (this).GenExprConvertOther(e, selfIdent, env, expectedOwnership, out _out51, out _out52, out _out53);
            r = _out51;
            resultingOwnership = _out52;
            readIdents = _out53;
          }
        }
      after_match0: ;
      }
      return ;
    }
    public void GenIdent(Dafny.ISequence<Dafny.Rune> rName, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      r = RAST.Expr.create_Identifier(rName);
      Std.Wrappers._IOption<RAST._IType> _0_tpe;
      _0_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1_placeboOpt;
      if ((_0_tpe).is_Some) {
        _1_placeboOpt = ((_0_tpe).dtor_value).ExtractMaybePlacebo();
      } else {
        _1_placeboOpt = Std.Wrappers.Option<RAST._IType>.create_None();
      }
      bool _2_currentlyBorrowed;
      _2_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _3_noNeedOfClone;
      _3_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply0();
        _2_currentlyBorrowed = false;
        _3_noNeedOfClone = true;
        _0_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        if (_2_currentlyBorrowed) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        } else {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
        }
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_0_tpe).is_Some) && (((_0_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _4_needObjectFromRef;
        _4_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source0 = (selfIdent).dtor_dafnyType;
          {
            if (_source0.is_UserDefined) {
              DAST._IResolvedType resolved0 = _source0.dtor_resolved;
              DAST._IResolvedTypeBase _5_base = resolved0.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _6_attributes = resolved0.dtor_attributes;
              return ((_5_base).is_Class) || ((_5_base).is_Trait);
            }
          }
          {
            return false;
          }
        }))());
        if (_4_needObjectFromRef) {
          r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_3_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_3_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_2_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_0_tpe).is_Some) && (((_0_tpe).dtor_value).IsPointer())) {
            r = ((this).read__macro).Apply1(r);
          } else {
            r = RAST.__default.Borrow(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      }
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(rName);
      return ;
    }
    public bool HasExternAttributeRenamingModule(Dafny.ISequence<DAST._IAttribute> attributes) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_0_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_0_attributes).UniqueElements, false, (((_exists_var_0) => {
        DAST._IAttribute _1_attribute = (DAST._IAttribute)_exists_var_0;
        return ((_0_attributes).Contains(_1_attribute)) && ((((_1_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1_attribute).dtor_args).Count)) == (new BigInteger(2))));
      }))))(attributes);
    }
    public void GenArgs(DCOMP._ISelfInfo selfIdent, DAST._ICallName name, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, DCOMP._IEnvironment env, out Dafny.ISequence<RAST._IExpr> argExprs, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out Dafny.ISequence<RAST._IType> typeExprs, out Std.Wrappers._IOption<DAST._IResolvedType> fullNameQualifier)
    {
      argExprs = Dafny.Sequence<RAST._IExpr>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      typeExprs = Dafny.Sequence<RAST._IType>.Empty;
      fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.Default();
      argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.ISequence<DAST._IFormal> _0_signature;
      if ((name).is_CallName) {
        if ((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) {
          _0_signature = Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature));
        } else {
          _0_signature = ((name).dtor_signature);
        }
      } else {
        _0_signature = Dafny.Sequence<DAST._IFormal>.FromElements();
      }
      BigInteger _hi0 = new BigInteger((args).Count);
      for (BigInteger _1_i = BigInteger.Zero; _1_i < _hi0; _1_i++) {
        DCOMP._IOwnership _2_argOwnership;
        _2_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_1_i) < (new BigInteger((_0_signature).Count))) {
          RAST._IType _3_tpe;
          RAST._IType _out0;
          _out0 = (this).GenType(((_0_signature).Select(_1_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _3_tpe = _out0;
          if ((_3_tpe).CanReadWithoutClone()) {
            _2_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _4_argExpr;
        DCOMP._IOwnership _5___v155;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _6_argIdents;
        RAST._IExpr _out1;
        DCOMP._IOwnership _out2;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out3;
        (this).GenExpr((args).Select(_1_i), selfIdent, env, _2_argOwnership, out _out1, out _out2, out _out3);
        _4_argExpr = _out1;
        _5___v155 = _out2;
        _6_argIdents = _out3;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_4_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _6_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi1 = new BigInteger((typeArgs).Count);
      for (BigInteger _7_typeI = BigInteger.Zero; _7_typeI < _hi1; _7_typeI++) {
        RAST._IType _8_typeExpr;
        RAST._IType _out4;
        _out4 = (this).GenType((typeArgs).Select(_7_typeI), DCOMP.GenTypeContext.@default());
        _8_typeExpr = _out4;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_8_typeExpr));
      }
      DAST._ICallName _source0 = name;
      {
        if (_source0.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _9_nameIdent = _source0.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType0 = _source0.dtor_onType;
          if (onType0.is_Some) {
            DAST._IType value0 = onType0.dtor_value;
            if (value0.is_UserDefined) {
              DAST._IResolvedType _10_resolvedType = value0.dtor_resolved;
              if ((((_10_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_11_resolvedType, _12_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_12_nameIdent), true, (((_forall_var_0) => {
                Dafny.ISequence<Dafny.Rune> _13_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_0;
                return !(((_11_resolvedType).dtor_properMethods).Contains(_13_m)) || (!object.Equals(_13_m, _12_nameIdent));
              }))))(_10_resolvedType, _9_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_10_resolvedType, (_9_nameIdent)), _10_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
              goto after_match0;
            }
          }
        }
      }
      {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    after_match0: ;
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> GetMethodName(DAST._IExpression @on, DAST._ICallName name)
    {
      DAST._ICallName _source0 = name;
      {
        if (_source0.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _0_ident = _source0.dtor_name;
          if ((@on).is_ExternCompanion) {
            return (_0_ident);
          } else {
            return DCOMP.__default.escapeName(_0_ident);
          }
        }
      }
      {
        bool disjunctiveMatch0 = false;
        if (_source0.is_MapBuilderAdd) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetBuilderAdd) {
          disjunctiveMatch0 = true;
        }
        if (disjunctiveMatch0) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
        }
      }
      {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
      }
    }
    public void GenExpr(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source0 = e;
      {
        if (_source0.is_Literal) {
          RAST._IExpr _out0;
          DCOMP._IOwnership _out1;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out0, out _out1, out _out2);
          r = _out0;
          resultingOwnership = _out1;
          readIdents = _out2;
          goto after_match0;
        }
      }
      {
        if (_source0.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _0_name = _source0.dtor_name;
          {
            RAST._IExpr _out3;
            DCOMP._IOwnership _out4;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
            (this).GenIdent(DCOMP.__default.escapeVar(_0_name), selfIdent, env, expectedOwnership, out _out3, out _out4, out _out5);
            r = _out3;
            resultingOwnership = _out4;
            readIdents = _out5;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1_path = _source0.dtor_ExternCompanion_a0;
          {
            RAST._IExpr _out6;
            _out6 = DCOMP.COMP.GenPathExpr(_1_path, false);
            r = _out6;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out7;
              DCOMP._IOwnership _out8;
              (this).FromOwned(r, expectedOwnership, out _out7, out _out8);
              r = _out7;
              resultingOwnership = _out8;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2_path = _source0.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _3_typeArgs = _source0.dtor_typeArgs;
          {
            RAST._IExpr _out9;
            _out9 = DCOMP.COMP.GenPathExpr(_2_path, true);
            r = _out9;
            if ((new BigInteger((_3_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _4_typeExprs;
              _4_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi0 = new BigInteger((_3_typeArgs).Count);
              for (BigInteger _5_i = BigInteger.Zero; _5_i < _hi0; _5_i++) {
                RAST._IType _6_typeExpr;
                RAST._IType _out10;
                _out10 = (this).GenType((_3_typeArgs).Select(_5_i), DCOMP.GenTypeContext.@default());
                _6_typeExpr = _out10;
                _4_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_4_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_6_typeExpr));
              }
              r = (r).ApplyType(_4_typeExprs);
            }
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out11;
              DCOMP._IOwnership _out12;
              (this).FromOwned(r, expectedOwnership, out _out11, out _out12);
              r = _out11;
              resultingOwnership = _out12;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_InitializationValue) {
          DAST._IType _7_typ = _source0.dtor_typ;
          {
            RAST._IType _8_typExpr;
            RAST._IType _out13;
            _out13 = (this).GenType(_7_typ, DCOMP.GenTypeContext.@default());
            _8_typExpr = _out13;
            if ((_8_typExpr).IsObjectOrPointer()) {
              r = (_8_typExpr).ToNullExpr();
            } else {
              r = ((RAST.Expr.create_TraitCast(_8_typExpr, RAST.__default.DefaultTrait)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).Apply0();
            }
            RAST._IExpr _out14;
            DCOMP._IOwnership _out15;
            (this).FromOwned(r, expectedOwnership, out _out14, out _out15);
            r = _out14;
            resultingOwnership = _out15;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _9_values = _source0.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IExpr> _10_exprs;
            _10_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi1 = new BigInteger((_9_values).Count);
            for (BigInteger _11_i = BigInteger.Zero; _11_i < _hi1; _11_i++) {
              RAST._IExpr _12_recursiveGen;
              DCOMP._IOwnership _13___v165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14_recIdents;
              RAST._IExpr _out16;
              DCOMP._IOwnership _out17;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out18;
              (this).GenExpr((_9_values).Select(_11_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out16, out _out17, out _out18);
              _12_recursiveGen = _out16;
              _13___v165 = _out17;
              _14_recIdents = _out18;
              _10_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_10_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_12_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _14_recIdents);
            }
            if ((new BigInteger((_9_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              r = RAST.Expr.create_Tuple(_10_exprs);
            } else {
              r = RAST.__default.SystemTuple(_10_exprs);
            }
            RAST._IExpr _out19;
            DCOMP._IOwnership _out20;
            (this).FromOwned(r, expectedOwnership, out _out19, out _out20);
            r = _out19;
            resultingOwnership = _out20;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _15_path = _source0.dtor_path;
          Dafny.ISequence<DAST._IType> _16_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _17_args = _source0.dtor_args;
          {
            RAST._IExpr _out21;
            _out21 = DCOMP.COMP.GenPathExpr(_15_path, true);
            r = _out21;
            if ((new BigInteger((_16_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _18_typeExprs;
              _18_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi2 = new BigInteger((_16_typeArgs).Count);
              for (BigInteger _19_i = BigInteger.Zero; _19_i < _hi2; _19_i++) {
                RAST._IType _20_typeExpr;
                RAST._IType _out22;
                _out22 = (this).GenType((_16_typeArgs).Select(_19_i), DCOMP.GenTypeContext.@default());
                _20_typeExpr = _out22;
                _18_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_18_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_20_typeExpr));
              }
              r = (r).ApplyType(_18_typeExprs);
            }
            r = (r).FSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _21_arguments;
            _21_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi3 = new BigInteger((_17_args).Count);
            for (BigInteger _22_i = BigInteger.Zero; _22_i < _hi3; _22_i++) {
              RAST._IExpr _23_recursiveGen;
              DCOMP._IOwnership _24___v166;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _25_recIdents;
              RAST._IExpr _out23;
              DCOMP._IOwnership _out24;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out25;
              (this).GenExpr((_17_args).Select(_22_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out23, out _out24, out _out25);
              _23_recursiveGen = _out23;
              _24___v166 = _out24;
              _25_recIdents = _out25;
              _21_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_21_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_23_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _25_recIdents);
            }
            r = (r).Apply(_21_arguments);
            RAST._IExpr _out26;
            DCOMP._IOwnership _out27;
            (this).FromOwned(r, expectedOwnership, out _out26, out _out27);
            r = _out26;
            resultingOwnership = _out27;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _26_dims = _source0.dtor_dims;
          DAST._IType _27_typ = _source0.dtor_typ;
          {
            if ((new BigInteger(16)) < (new BigInteger((_26_dims).Count))) {
              RAST._IExpr _out28;
              _out28 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions"), (this).InitEmptyExpr());
              r = _out28;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = (this).InitEmptyExpr();
              RAST._IType _28_typeGen;
              RAST._IType _out29;
              _out29 = (this).GenType(_27_typ, DCOMP.GenTypeContext.@default());
              _28_typeGen = _out29;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _29_dimExprs;
              _29_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi4 = new BigInteger((_26_dims).Count);
              for (BigInteger _30_i = BigInteger.Zero; _30_i < _hi4; _30_i++) {
                RAST._IExpr _31_recursiveGen;
                DCOMP._IOwnership _32___v167;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _33_recIdents;
                RAST._IExpr _out30;
                DCOMP._IOwnership _out31;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
                (this).GenExpr((_26_dims).Select(_30_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
                _31_recursiveGen = _out30;
                _32___v167 = _out31;
                _33_recIdents = _out32;
                _29_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_29_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_31_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _33_recIdents);
              }
              if ((new BigInteger((_26_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _34_class__name;
                _34_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_26_dims).Count)));
                r = (((((RAST.__default.dafny__runtime).MSel(_34_class__name)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_28_typeGen))).FSel((this).placebos__usize)).Apply(_29_dimExprs);
              } else {
                r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_28_typeGen))).Apply(_29_dimExprs);
              }
            }
            RAST._IExpr _out33;
            DCOMP._IOwnership _out34;
            (this).FromOwned(r, expectedOwnership, out _out33, out _out34);
            r = _out33;
            resultingOwnership = _out34;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ArrayIndexToInt) {
          DAST._IExpression _35_underlying = _source0.dtor_value;
          {
            RAST._IExpr _36_recursiveGen;
            DCOMP._IOwnership _37___v168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _38_recIdents;
            RAST._IExpr _out35;
            DCOMP._IOwnership _out36;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out37;
            (this).GenExpr(_35_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out35, out _out36, out _out37);
            _36_recursiveGen = _out35;
            _37___v168 = _out36;
            _38_recIdents = _out37;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(_36_recursiveGen);
            readIdents = _38_recIdents;
            RAST._IExpr _out38;
            DCOMP._IOwnership _out39;
            (this).FromOwned(r, expectedOwnership, out _out38, out _out39);
            r = _out38;
            resultingOwnership = _out39;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_FinalizeNewArray) {
          DAST._IExpression _39_underlying = _source0.dtor_value;
          DAST._IType _40_typ = _source0.dtor_typ;
          {
            RAST._IType _41_tpe;
            RAST._IType _out40;
            _out40 = (this).GenType(_40_typ, DCOMP.GenTypeContext.@default());
            _41_tpe = _out40;
            RAST._IExpr _42_recursiveGen;
            DCOMP._IOwnership _43___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _44_recIdents;
            RAST._IExpr _out41;
            DCOMP._IOwnership _out42;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out43;
            (this).GenExpr(_39_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out41, out _out42, out _out43);
            _42_recursiveGen = _out41;
            _43___v169 = _out42;
            _44_recIdents = _out43;
            readIdents = _44_recIdents;
            if ((_41_tpe).IsObjectOrPointer()) {
              RAST._IType _45_t;
              _45_t = (_41_tpe).ObjectOrPointerUnderlying();
              if ((_45_t).is_Array) {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).array__construct)).Apply1(_42_recursiveGen);
              } else if ((_45_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _46_c;
                _46_c = (_45_t).MultiArrayClass();
                r = ((((RAST.__default.dafny__runtime).MSel(_46_c)).AsExpr()).FSel((this).array__construct)).Apply1(_42_recursiveGen);
              } else {
                RAST._IExpr _out44;
                _out44 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_41_tpe)._ToString(DCOMP.__default.IND)), (this).InitEmptyExpr());
                r = _out44;
              }
            } else {
              RAST._IExpr _out45;
              _out45 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_41_tpe)._ToString(DCOMP.__default.IND)), (this).InitEmptyExpr());
              r = _out45;
            }
            RAST._IExpr _out46;
            DCOMP._IOwnership _out47;
            (this).FromOwned(r, expectedOwnership, out _out46, out _out47);
            r = _out46;
            resultingOwnership = _out47;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_DatatypeValue) {
          DAST._IResolvedType _47_datatypeType = _source0.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _48_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _49_variant = _source0.dtor_variant;
          bool _50_isCo = _source0.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _51_values = _source0.dtor_contents;
          {
            RAST._IExpr _out48;
            _out48 = DCOMP.COMP.GenPathExpr((_47_datatypeType).dtor_path, true);
            r = _out48;
            Dafny.ISequence<RAST._IType> _52_genTypeArgs;
            _52_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi5 = new BigInteger((_48_typeArgs).Count);
            for (BigInteger _53_i = BigInteger.Zero; _53_i < _hi5; _53_i++) {
              RAST._IType _54_typeExpr;
              RAST._IType _out49;
              _out49 = (this).GenType((_48_typeArgs).Select(_53_i), DCOMP.GenTypeContext.@default());
              _54_typeExpr = _out49;
              _52_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_52_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_54_typeExpr));
            }
            if ((new BigInteger((_48_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_52_genTypeArgs);
            }
            r = (r).FSel(DCOMP.__default.escapeName(_49_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _55_assignments;
            _55_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi6 = new BigInteger((_51_values).Count);
            for (BigInteger _56_i = BigInteger.Zero; _56_i < _hi6; _56_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_51_values).Select(_56_i);
              Dafny.ISequence<Dafny.Rune> _57_name = _let_tmp_rhs0.dtor__0;
              DAST._IExpression _58_value = _let_tmp_rhs0.dtor__1;
              if (_50_isCo) {
                RAST._IExpr _59_recursiveGen;
                DCOMP._IOwnership _60___v170;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _61_recIdents;
                RAST._IExpr _out50;
                DCOMP._IOwnership _out51;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out52;
                (this).GenExpr(_58_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out50, out _out51, out _out52);
                _59_recursiveGen = _out50;
                _60___v170 = _out51;
                _61_recIdents = _out52;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _61_recIdents);
                RAST._IExpr _62_allReadCloned;
                _62_allReadCloned = (this).InitEmptyExpr();
                while (!(_61_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _63_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_61_recIdents).Elements) {
                    _63_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                    if ((_61_recIdents).Contains(_63_next)) {
                      goto after__ASSIGN_SUCH_THAT_0;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value");
                after__ASSIGN_SUCH_THAT_0: ;
                  _62_allReadCloned = (_62_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _63_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some((RAST.Expr.create_Identifier(_63_next)).Clone())));
                  _61_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_61_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_63_next));
                }
                RAST._IExpr _64_wasAssigned;
                _64_wasAssigned = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsExpr()).Apply1(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Lazy"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply1((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("boxed"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Box"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply1((_62_allReadCloned).Then(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_None(), _59_recursiveGen)))));
                _55_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_55_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_57_name), _64_wasAssigned)));
              } else {
                RAST._IExpr _65_recursiveGen;
                DCOMP._IOwnership _66___v171;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _67_recIdents;
                RAST._IExpr _out53;
                DCOMP._IOwnership _out54;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out55;
                (this).GenExpr(_58_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out53, out _out54, out _out55);
                _65_recursiveGen = _out53;
                _66___v171 = _out54;
                _67_recIdents = _out55;
                _55_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_55_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_57_name), _65_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _67_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _55_assignments);
            if ((this).IsRcWrapped((_47_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out56;
            DCOMP._IOwnership _out57;
            (this).FromOwned(r, expectedOwnership, out _out56, out _out57);
            r = _out56;
            resultingOwnership = _out57;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Convert) {
          {
            RAST._IExpr _out58;
            DCOMP._IOwnership _out59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out58, out _out59, out _out60);
            r = _out58;
            resultingOwnership = _out59;
            readIdents = _out60;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqConstruct) {
          DAST._IExpression _68_length = _source0.dtor_length;
          DAST._IExpression _69_expr = _source0.dtor_elem;
          {
            RAST._IExpr _70_recursiveGen;
            DCOMP._IOwnership _71___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _72_recIdents;
            RAST._IExpr _out61;
            DCOMP._IOwnership _out62;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out63;
            (this).GenExpr(_69_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out61, out _out62, out _out63);
            _70_recursiveGen = _out61;
            _71___v175 = _out62;
            _72_recIdents = _out63;
            RAST._IExpr _73_lengthGen;
            DCOMP._IOwnership _74___v176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _75_lengthIdents;
            RAST._IExpr _out64;
            DCOMP._IOwnership _out65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
            (this).GenExpr(_68_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out64, out _out65, out _out66);
            _73_lengthGen = _out64;
            _74___v176 = _out65;
            _75_lengthIdents = _out66;
            r = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_initializer"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_70_recursiveGen));
            RAST._IExpr _76_range;
            _76_range = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr();
            _76_range = (_76_range).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Zero"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("zero"))).Apply0(), _73_lengthGen));
            _76_range = (_76_range).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map"));
            RAST._IExpr _77_rangeMap;
            _77_rangeMap = RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.ImplicitlyTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i"))), Std.Wrappers.Option<RAST._IType>.create_None(), (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_initializer"))).Apply1(RAST.__default.Borrow(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i")))));
            _76_range = (_76_range).Apply1(_77_rangeMap);
            _76_range = (((_76_range).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("collect"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))))).Apply0();
            r = RAST.Expr.create_Block((r).Then(_76_range));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_72_recIdents, _75_lengthIdents);
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            (this).FromOwned(r, expectedOwnership, out _out67, out _out68);
            r = _out67;
            resultingOwnership = _out68;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _78_exprs = _source0.dtor_elements;
          DAST._IType _79_typ = _source0.dtor_typ;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _80_genTpe;
            RAST._IType _out69;
            _out69 = (this).GenType(_79_typ, DCOMP.GenTypeContext.@default());
            _80_genTpe = _out69;
            BigInteger _81_i;
            _81_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _82_args;
            _82_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_81_i) < (new BigInteger((_78_exprs).Count))) {
              RAST._IExpr _83_recursiveGen;
              DCOMP._IOwnership _84___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _85_recIdents;
              RAST._IExpr _out70;
              DCOMP._IOwnership _out71;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out72;
              (this).GenExpr((_78_exprs).Select(_81_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out70, out _out71, out _out72);
              _83_recursiveGen = _out70;
              _84___v177 = _out71;
              _85_recIdents = _out72;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _85_recIdents);
              _82_args = Dafny.Sequence<RAST._IExpr>.Concat(_82_args, Dafny.Sequence<RAST._IExpr>.FromElements(_83_recursiveGen));
              _81_i = (_81_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_82_args);
            if ((new BigInteger((_82_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply1(_80_genTpe));
            }
            RAST._IExpr _out73;
            DCOMP._IOwnership _out74;
            (this).FromOwned(r, expectedOwnership, out _out73, out _out74);
            r = _out73;
            resultingOwnership = _out74;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _86_exprs = _source0.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _87_generatedValues;
            _87_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _88_i;
            _88_i = BigInteger.Zero;
            while ((_88_i) < (new BigInteger((_86_exprs).Count))) {
              RAST._IExpr _89_recursiveGen;
              DCOMP._IOwnership _90___v178;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _91_recIdents;
              RAST._IExpr _out75;
              DCOMP._IOwnership _out76;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out77;
              (this).GenExpr((_86_exprs).Select(_88_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out75, out _out76, out _out77);
              _89_recursiveGen = _out75;
              _90___v178 = _out76;
              _91_recIdents = _out77;
              _87_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_87_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_89_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _91_recIdents);
              _88_i = (_88_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).AsExpr()).Apply(_87_generatedValues);
            RAST._IExpr _out78;
            DCOMP._IOwnership _out79;
            (this).FromOwned(r, expectedOwnership, out _out78, out _out79);
            r = _out78;
            resultingOwnership = _out79;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _92_exprs = _source0.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _93_generatedValues;
            _93_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _94_i;
            _94_i = BigInteger.Zero;
            while ((_94_i) < (new BigInteger((_92_exprs).Count))) {
              RAST._IExpr _95_recursiveGen;
              DCOMP._IOwnership _96___v179;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _97_recIdents;
              RAST._IExpr _out80;
              DCOMP._IOwnership _out81;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out82;
              (this).GenExpr((_92_exprs).Select(_94_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out80, out _out81, out _out82);
              _95_recursiveGen = _out80;
              _96___v179 = _out81;
              _97_recIdents = _out82;
              _93_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_93_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_95_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _97_recIdents);
              _94_i = (_94_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).AsExpr()).Apply(_93_generatedValues);
            RAST._IExpr _out83;
            DCOMP._IOwnership _out84;
            (this).FromOwned(r, expectedOwnership, out _out83, out _out84);
            r = _out83;
            resultingOwnership = _out84;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ToMultiset) {
          DAST._IExpression _98_expr = _source0.dtor_ToMultiset_a0;
          {
            RAST._IExpr _99_recursiveGen;
            DCOMP._IOwnership _100___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _101_recIdents;
            RAST._IExpr _out85;
            DCOMP._IOwnership _out86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out87;
            (this).GenExpr(_98_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out85, out _out86, out _out87);
            _99_recursiveGen = _out85;
            _100___v180 = _out86;
            _101_recIdents = _out87;
            r = ((_99_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply0();
            readIdents = _101_recIdents;
            RAST._IExpr _out88;
            DCOMP._IOwnership _out89;
            (this).FromOwned(r, expectedOwnership, out _out88, out _out89);
            r = _out88;
            resultingOwnership = _out89;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _102_mapElems = _source0.dtor_mapElems;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _103_generatedValues;
            _103_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _104_i;
            _104_i = BigInteger.Zero;
            while ((_104_i) < (new BigInteger((_102_mapElems).Count))) {
              RAST._IExpr _105_recursiveGenKey;
              DCOMP._IOwnership _106___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _107_recIdentsKey;
              RAST._IExpr _out90;
              DCOMP._IOwnership _out91;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out92;
              (this).GenExpr(((_102_mapElems).Select(_104_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out90, out _out91, out _out92);
              _105_recursiveGenKey = _out90;
              _106___v181 = _out91;
              _107_recIdentsKey = _out92;
              RAST._IExpr _108_recursiveGenValue;
              DCOMP._IOwnership _109___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _110_recIdentsValue;
              RAST._IExpr _out93;
              DCOMP._IOwnership _out94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out95;
              (this).GenExpr(((_102_mapElems).Select(_104_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out93, out _out94, out _out95);
              _108_recursiveGenValue = _out93;
              _109___v182 = _out94;
              _110_recIdentsValue = _out95;
              _103_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_103_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_105_recursiveGenKey, _108_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _107_recIdentsKey), _110_recIdentsValue);
              _104_i = (_104_i) + (BigInteger.One);
            }
            _104_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _111_arguments;
            _111_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_104_i) < (new BigInteger((_103_generatedValues).Count))) {
              RAST._IExpr _112_genKey;
              _112_genKey = ((_103_generatedValues).Select(_104_i)).dtor__0;
              RAST._IExpr _113_genValue;
              _113_genValue = ((_103_generatedValues).Select(_104_i)).dtor__1;
              _111_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_111_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _112_genKey, _113_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _104_i = (_104_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).AsExpr()).Apply(_111_arguments);
            RAST._IExpr _out96;
            DCOMP._IOwnership _out97;
            (this).FromOwned(r, expectedOwnership, out _out96, out _out97);
            r = _out96;
            resultingOwnership = _out97;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqUpdate) {
          DAST._IExpression _114_expr = _source0.dtor_expr;
          DAST._IExpression _115_index = _source0.dtor_indexExpr;
          DAST._IExpression _116_value = _source0.dtor_value;
          {
            RAST._IExpr _117_exprR;
            DCOMP._IOwnership _118___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _119_exprIdents;
            RAST._IExpr _out98;
            DCOMP._IOwnership _out99;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
            (this).GenExpr(_114_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out98, out _out99, out _out100);
            _117_exprR = _out98;
            _118___v183 = _out99;
            _119_exprIdents = _out100;
            RAST._IExpr _120_indexR;
            DCOMP._IOwnership _121_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _122_indexIdents;
            RAST._IExpr _out101;
            DCOMP._IOwnership _out102;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
            (this).GenExpr(_115_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out101, out _out102, out _out103);
            _120_indexR = _out101;
            _121_indexOwnership = _out102;
            _122_indexIdents = _out103;
            RAST._IExpr _123_valueR;
            DCOMP._IOwnership _124_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _125_valueIdents;
            RAST._IExpr _out104;
            DCOMP._IOwnership _out105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out106;
            (this).GenExpr(_116_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out104, out _out105, out _out106);
            _123_valueR = _out104;
            _124_valueOwnership = _out105;
            _125_valueIdents = _out106;
            r = ((_117_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_120_indexR, _123_valueR));
            RAST._IExpr _out107;
            DCOMP._IOwnership _out108;
            (this).FromOwned(r, expectedOwnership, out _out107, out _out108);
            r = _out107;
            resultingOwnership = _out108;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_119_exprIdents, _122_indexIdents), _125_valueIdents);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapUpdate) {
          DAST._IExpression _126_expr = _source0.dtor_expr;
          DAST._IExpression _127_index = _source0.dtor_indexExpr;
          DAST._IExpression _128_value = _source0.dtor_value;
          {
            RAST._IExpr _129_exprR;
            DCOMP._IOwnership _130___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _131_exprIdents;
            RAST._IExpr _out109;
            DCOMP._IOwnership _out110;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
            (this).GenExpr(_126_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out109, out _out110, out _out111);
            _129_exprR = _out109;
            _130___v184 = _out110;
            _131_exprIdents = _out111;
            RAST._IExpr _132_indexR;
            DCOMP._IOwnership _133_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _134_indexIdents;
            RAST._IExpr _out112;
            DCOMP._IOwnership _out113;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
            (this).GenExpr(_127_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out112, out _out113, out _out114);
            _132_indexR = _out112;
            _133_indexOwnership = _out113;
            _134_indexIdents = _out114;
            RAST._IExpr _135_valueR;
            DCOMP._IOwnership _136_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _137_valueIdents;
            RAST._IExpr _out115;
            DCOMP._IOwnership _out116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
            (this).GenExpr(_128_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out115, out _out116, out _out117);
            _135_valueR = _out115;
            _136_valueOwnership = _out116;
            _137_valueIdents = _out117;
            r = ((_129_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_132_indexR, _135_valueR));
            RAST._IExpr _out118;
            DCOMP._IOwnership _out119;
            (this).FromOwned(r, expectedOwnership, out _out118, out _out119);
            r = _out118;
            resultingOwnership = _out119;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_131_exprIdents, _134_indexIdents), _137_valueIdents);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_This) {
          {
            DCOMP._ISelfInfo _source1 = selfIdent;
            {
              if (_source1.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _138_id = _source1.dtor_rSelfName;
                DAST._IType _139_dafnyType = _source1.dtor_dafnyType;
                {
                  RAST._IExpr _out120;
                  DCOMP._IOwnership _out121;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
                  (this).GenIdent(_138_id, selfIdent, env, expectedOwnership, out _out120, out _out121, out _out122);
                  r = _out120;
                  resultingOwnership = _out121;
                  readIdents = _out122;
                }
                goto after_match1;
              }
            }
            {
              DCOMP._ISelfInfo _140_None = _source1;
              {
                RAST._IExpr _out123;
                _out123 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this outside of a method"), (this).InitEmptyExpr());
                r = _out123;
                RAST._IExpr _out124;
                DCOMP._IOwnership _out125;
                (this).FromOwned(r, expectedOwnership, out _out124, out _out125);
                r = _out124;
                resultingOwnership = _out125;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
          after_match1: ;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Ite) {
          DAST._IExpression _141_cond = _source0.dtor_cond;
          DAST._IExpression _142_t = _source0.dtor_thn;
          DAST._IExpression _143_f = _source0.dtor_els;
          {
            RAST._IExpr _144_cond;
            DCOMP._IOwnership _145___v185;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _146_recIdentsCond;
            RAST._IExpr _out126;
            DCOMP._IOwnership _out127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
            (this).GenExpr(_141_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out126, out _out127, out _out128);
            _144_cond = _out126;
            _145___v185 = _out127;
            _146_recIdentsCond = _out128;
            RAST._IExpr _147_fExpr;
            DCOMP._IOwnership _148_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _149_recIdentsF;
            RAST._IExpr _out129;
            DCOMP._IOwnership _out130;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
            (this).GenExpr(_143_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
            _147_fExpr = _out129;
            _148_fOwned = _out130;
            _149_recIdentsF = _out131;
            RAST._IExpr _150_tExpr;
            DCOMP._IOwnership _151___v186;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _152_recIdentsT;
            RAST._IExpr _out132;
            DCOMP._IOwnership _out133;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
            (this).GenExpr(_142_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out132, out _out133, out _out134);
            _150_tExpr = _out132;
            _151___v186 = _out133;
            _152_recIdentsT = _out134;
            r = RAST.Expr.create_IfExpr(_144_cond, _150_tExpr, _147_fExpr);
            RAST._IExpr _out135;
            DCOMP._IOwnership _out136;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out135, out _out136);
            r = _out135;
            resultingOwnership = _out136;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_146_recIdentsCond, _152_recIdentsT), _149_recIdentsF);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source0.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _153_e = _source0.dtor_expr;
            DAST.Format._IUnaryOpFormat _154_format = _source0.dtor_format1;
            {
              RAST._IExpr _155_recursiveGen;
              DCOMP._IOwnership _156___v187;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _157_recIdents;
              RAST._IExpr _out137;
              DCOMP._IOwnership _out138;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
              (this).GenExpr(_153_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out137, out _out138, out _out139);
              _155_recursiveGen = _out137;
              _156___v187 = _out138;
              _157_recIdents = _out139;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _155_recursiveGen, _154_format);
              RAST._IExpr _out140;
              DCOMP._IOwnership _out141;
              (this).FromOwned(r, expectedOwnership, out _out140, out _out141);
              r = _out140;
              resultingOwnership = _out141;
              readIdents = _157_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source0.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _158_e = _source0.dtor_expr;
            DAST.Format._IUnaryOpFormat _159_format = _source0.dtor_format1;
            {
              RAST._IExpr _160_recursiveGen;
              DCOMP._IOwnership _161___v188;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _162_recIdents;
              RAST._IExpr _out142;
              DCOMP._IOwnership _out143;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
              (this).GenExpr(_158_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out142, out _out143, out _out144);
              _160_recursiveGen = _out142;
              _161___v188 = _out143;
              _162_recIdents = _out144;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _160_recursiveGen, _159_format);
              RAST._IExpr _out145;
              DCOMP._IOwnership _out146;
              (this).FromOwned(r, expectedOwnership, out _out145, out _out146);
              r = _out145;
              resultingOwnership = _out146;
              readIdents = _162_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source0.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _163_e = _source0.dtor_expr;
            DAST.Format._IUnaryOpFormat _164_format = _source0.dtor_format1;
            {
              RAST._IExpr _165_recursiveGen;
              DCOMP._IOwnership _166_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _167_recIdents;
              RAST._IExpr _out147;
              DCOMP._IOwnership _out148;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
              (this).GenExpr(_163_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out147, out _out148, out _out149);
              _165_recursiveGen = _out147;
              _166_recOwned = _out148;
              _167_recIdents = _out149;
              r = ((_165_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply0();
              RAST._IExpr _out150;
              DCOMP._IOwnership _out151;
              (this).FromOwned(r, expectedOwnership, out _out150, out _out151);
              r = _out150;
              resultingOwnership = _out151;
              readIdents = _167_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_BinOp) {
          RAST._IExpr _out152;
          DCOMP._IOwnership _out153;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out154;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out152, out _out153, out _out154);
          r = _out152;
          resultingOwnership = _out153;
          readIdents = _out154;
          goto after_match0;
        }
      }
      {
        if (_source0.is_ArrayLen) {
          DAST._IExpression _168_expr = _source0.dtor_expr;
          DAST._IType _169_exprType = _source0.dtor_exprType;
          BigInteger _170_dim = _source0.dtor_dim;
          bool _171_native = _source0.dtor_native;
          {
            RAST._IExpr _172_recursiveGen;
            DCOMP._IOwnership _173___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _174_recIdents;
            RAST._IExpr _out155;
            DCOMP._IOwnership _out156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out157;
            (this).GenExpr(_168_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out155, out _out156, out _out157);
            _172_recursiveGen = _out155;
            _173___v193 = _out156;
            _174_recIdents = _out157;
            RAST._IType _175_arrayType;
            RAST._IType _out158;
            _out158 = (this).GenType(_169_exprType, DCOMP.GenTypeContext.@default());
            _175_arrayType = _out158;
            if (!((_175_arrayType).IsObjectOrPointer())) {
              RAST._IExpr _out159;
              _out159 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_175_arrayType)._ToString(DCOMP.__default.IND)), (this).InitEmptyExpr());
              r = _out159;
            } else {
              RAST._IType _176_underlying;
              _176_underlying = (_175_arrayType).ObjectOrPointerUnderlying();
              if (((_170_dim).Sign == 0) && ((_176_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_172_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply0();
              } else {
                if ((_170_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_172_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply0();
                } else {
                  r = ((((this).read__macro).Apply1(_172_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_170_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply0();
                }
              }
              if (!(_171_native)) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
              }
            }
            RAST._IExpr _out160;
            DCOMP._IOwnership _out161;
            (this).FromOwned(r, expectedOwnership, out _out160, out _out161);
            r = _out160;
            resultingOwnership = _out161;
            readIdents = _174_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapKeys) {
          DAST._IExpression _177_expr = _source0.dtor_expr;
          {
            RAST._IExpr _178_recursiveGen;
            DCOMP._IOwnership _179___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _180_recIdents;
            RAST._IExpr _out162;
            DCOMP._IOwnership _out163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
            (this).GenExpr(_177_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out162, out _out163, out _out164);
            _178_recursiveGen = _out162;
            _179___v194 = _out163;
            _180_recIdents = _out164;
            readIdents = _180_recIdents;
            r = ((_178_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply0();
            RAST._IExpr _out165;
            DCOMP._IOwnership _out166;
            (this).FromOwned(r, expectedOwnership, out _out165, out _out166);
            r = _out165;
            resultingOwnership = _out166;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapValues) {
          DAST._IExpression _181_expr = _source0.dtor_expr;
          {
            RAST._IExpr _182_recursiveGen;
            DCOMP._IOwnership _183___v195;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _184_recIdents;
            RAST._IExpr _out167;
            DCOMP._IOwnership _out168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
            (this).GenExpr(_181_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out167, out _out168, out _out169);
            _182_recursiveGen = _out167;
            _183___v195 = _out168;
            _184_recIdents = _out169;
            readIdents = _184_recIdents;
            r = ((_182_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply0();
            RAST._IExpr _out170;
            DCOMP._IOwnership _out171;
            (this).FromOwned(r, expectedOwnership, out _out170, out _out171);
            r = _out170;
            resultingOwnership = _out171;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapItems) {
          DAST._IExpression _185_expr = _source0.dtor_expr;
          {
            RAST._IExpr _186_recursiveGen;
            DCOMP._IOwnership _187___v196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _188_recIdents;
            RAST._IExpr _out172;
            DCOMP._IOwnership _out173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out174;
            (this).GenExpr(_185_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out172, out _out173, out _out174);
            _186_recursiveGen = _out172;
            _187___v196 = _out173;
            _188_recIdents = _out174;
            readIdents = _188_recIdents;
            r = ((_186_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply0();
            RAST._IExpr _out175;
            DCOMP._IOwnership _out176;
            (this).FromOwned(r, expectedOwnership, out _out175, out _out176);
            r = _out175;
            resultingOwnership = _out176;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SelectFn) {
          DAST._IExpression _189_on = _source0.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _190_field = _source0.dtor_field;
          bool _191_isDatatype = _source0.dtor_onDatatype;
          bool _192_isStatic = _source0.dtor_isStatic;
          bool _193_isConstant = _source0.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _194_arguments = _source0.dtor_arguments;
          {
            RAST._IExpr _195_onExpr;
            DCOMP._IOwnership _196_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _197_recIdents;
            RAST._IExpr _out177;
            DCOMP._IOwnership _out178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out179;
            (this).GenExpr(_189_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out177, out _out178, out _out179);
            _195_onExpr = _out177;
            _196_onOwned = _out178;
            _197_recIdents = _out179;
            Dafny.ISequence<Dafny.Rune> _198_onString;
            _198_onString = (_195_onExpr)._ToString(DCOMP.__default.IND);
            DCOMP._IEnvironment _199_lEnv;
            _199_lEnv = env;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _200_args;
            _200_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _201_parameters;
            _201_parameters = Dafny.Sequence<RAST._IFormal>.FromElements();
            BigInteger _hi7 = new BigInteger((_194_arguments).Count);
            for (BigInteger _202_i = BigInteger.Zero; _202_i < _hi7; _202_i++) {
              RAST._IType _203_ty;
              RAST._IType _out180;
              _out180 = (this).GenType((_194_arguments).Select(_202_i), DCOMP.GenTypeContext.@default());
              _203_ty = _out180;
              RAST._IType _204_bTy;
              _204_bTy = RAST.Type.create_Borrowed(_203_ty);
              Dafny.ISequence<Dafny.Rune> _205_name;
              _205_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_202_i));
              _199_lEnv = (_199_lEnv).AddAssigned(_205_name, _204_bTy);
              _201_parameters = Dafny.Sequence<RAST._IFormal>.Concat(_201_parameters, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_205_name, _204_bTy)));
              _200_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_200_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_205_name, _203_ty)));
            }
            RAST._IExpr _206_body;
            if (_192_isStatic) {
              _206_body = (_195_onExpr).FSel(DCOMP.__default.escapeVar(_190_field));
            } else {
              _206_body = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget"))).Sel(DCOMP.__default.escapeVar(_190_field));
            }
            if (_193_isConstant) {
              _206_body = (_206_body).Apply0();
            }
            Dafny.ISequence<RAST._IExpr> _207_onExprArgs;
            _207_onExprArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi8 = new BigInteger((_200_args).Count);
            for (BigInteger _208_i = BigInteger.Zero; _208_i < _hi8; _208_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs1 = (_200_args).Select(_208_i);
              Dafny.ISequence<Dafny.Rune> _209_name = _let_tmp_rhs1.dtor__0;
              RAST._IType _210_ty = _let_tmp_rhs1.dtor__1;
              RAST._IExpr _211_rIdent;
              DCOMP._IOwnership _212___v197;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _213___v198;
              RAST._IExpr _out181;
              DCOMP._IOwnership _out182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out183;
              (this).GenIdent(_209_name, selfIdent, _199_lEnv, (((_210_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out181, out _out182, out _out183);
              _211_rIdent = _out181;
              _212___v197 = _out182;
              _213___v198 = _out183;
              _207_onExprArgs = Dafny.Sequence<RAST._IExpr>.Concat(_207_onExprArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_211_rIdent));
            }
            _206_body = (_206_body).Apply(_207_onExprArgs);
            r = RAST.Expr.create_Lambda(_201_parameters, Std.Wrappers.Option<RAST._IType>.create_None(), _206_body);
            if (_192_isStatic) {
            } else {
              RAST._IExpr _214_target;
              if (object.Equals(_196_onOwned, DCOMP.Ownership.create_OwnershipOwned())) {
                _214_target = _195_onExpr;
              } else {
                _214_target = (_195_onExpr).Clone();
              }
              r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_214_target))).Then(r));
            }
            Dafny.ISequence<RAST._IType> _215_typeShapeArgs;
            _215_typeShapeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi9 = new BigInteger((_194_arguments).Count);
            for (BigInteger _216_i = BigInteger.Zero; _216_i < _hi9; _216_i++) {
              _215_typeShapeArgs = Dafny.Sequence<RAST._IType>.Concat(_215_typeShapeArgs, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")))));
            }
            RAST._IType _217_typeShape;
            _217_typeShape = RAST.Type.create_DynType(RAST.Type.create_FnType(_215_typeShapeArgs, RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))));
            r = RAST.Expr.create_TypeAscription((RAST.__default.std__rc__Rc__new).Apply1(r), ((RAST.__default.std__rc__Rc).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_217_typeShape)));
            RAST._IExpr _out184;
            DCOMP._IOwnership _out185;
            (this).FromOwned(r, expectedOwnership, out _out184, out _out185);
            r = _out184;
            resultingOwnership = _out185;
            readIdents = _197_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Select) {
          DAST._IExpression _218_on = _source0.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _219_field = _source0.dtor_field;
          bool _220_isConstant = _source0.dtor_isConstant;
          bool _221_isDatatype = _source0.dtor_onDatatype;
          DAST._IType _222_fieldType = _source0.dtor_fieldType;
          {
            if (((_218_on).is_Companion) || ((_218_on).is_ExternCompanion)) {
              RAST._IExpr _223_onExpr;
              DCOMP._IOwnership _224_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _225_recIdents;
              RAST._IExpr _out186;
              DCOMP._IOwnership _out187;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
              (this).GenExpr(_218_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out186, out _out187, out _out188);
              _223_onExpr = _out186;
              _224_onOwned = _out187;
              _225_recIdents = _out188;
              r = ((_223_onExpr).FSel(DCOMP.__default.escapeVar(_219_field))).Apply0();
              RAST._IExpr _out189;
              DCOMP._IOwnership _out190;
              (this).FromOwned(r, expectedOwnership, out _out189, out _out190);
              r = _out189;
              resultingOwnership = _out190;
              readIdents = _225_recIdents;
              return ;
            } else if (_221_isDatatype) {
              RAST._IExpr _226_onExpr;
              DCOMP._IOwnership _227_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _228_recIdents;
              RAST._IExpr _out191;
              DCOMP._IOwnership _out192;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
              (this).GenExpr(_218_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out191, out _out192, out _out193);
              _226_onExpr = _out191;
              _227_onOwned = _out192;
              _228_recIdents = _out193;
              r = ((_226_onExpr).Sel(DCOMP.__default.escapeVar(_219_field))).Apply0();
              RAST._IType _229_typ;
              RAST._IType _out194;
              _out194 = (this).GenType(_222_fieldType, DCOMP.GenTypeContext.@default());
              _229_typ = _out194;
              RAST._IExpr _out195;
              DCOMP._IOwnership _out196;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out195, out _out196);
              r = _out195;
              resultingOwnership = _out196;
              readIdents = _228_recIdents;
            } else {
              RAST._IExpr _230_onExpr;
              DCOMP._IOwnership _231_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _232_recIdents;
              RAST._IExpr _out197;
              DCOMP._IOwnership _out198;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out199;
              (this).GenExpr(_218_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out197, out _out198, out _out199);
              _230_onExpr = _out197;
              _231_onOwned = _out198;
              _232_recIdents = _out199;
              r = _230_onExpr;
              if (!object.Equals(_230_onExpr, RAST.__default.self)) {
                RAST._IExpr _source2 = _230_onExpr;
                {
                  if (_source2.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op10 = _source2.dtor_op1;
                    if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying0 = _source2.dtor_underlying;
                      if (underlying0.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name0 = underlying0.dtor_name;
                        if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                          goto after_match2;
                        }
                      }
                    }
                  }
                }
                {
                }
              after_match2: ;
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                if (((this).ObjectType).is_RawPointers) {
                  r = ((this).read__macro).Apply1(r);
                } else {
                  r = ((this).modify__macro).Apply1(r);
                }
              }
              r = (r).Sel(DCOMP.__default.escapeVar(_219_field));
              if (_220_isConstant) {
                r = (r).Apply0();
              }
              r = (r).Clone();
              RAST._IExpr _out200;
              DCOMP._IOwnership _out201;
              (this).FromOwned(r, expectedOwnership, out _out200, out _out201);
              r = _out200;
              resultingOwnership = _out201;
              readIdents = _232_recIdents;
            }
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Index) {
          DAST._IExpression _233_on = _source0.dtor_expr;
          DAST._ICollKind _234_collKind = _source0.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _235_indices = _source0.dtor_indices;
          {
            RAST._IExpr _236_onExpr;
            DCOMP._IOwnership _237_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _238_recIdents;
            RAST._IExpr _out202;
            DCOMP._IOwnership _out203;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
            (this).GenExpr(_233_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out202, out _out203, out _out204);
            _236_onExpr = _out202;
            _237_onOwned = _out203;
            _238_recIdents = _out204;
            readIdents = _238_recIdents;
            r = _236_onExpr;
            bool _239_hadArray;
            _239_hadArray = false;
            if (object.Equals(_234_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _239_hadArray = true;
              if ((new BigInteger((_235_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi10 = new BigInteger((_235_indices).Count);
            for (BigInteger _240_i = BigInteger.Zero; _240_i < _hi10; _240_i++) {
              if (object.Equals(_234_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _241_idx;
                DCOMP._IOwnership _242_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _243_recIdentsIdx;
                RAST._IExpr _out205;
                DCOMP._IOwnership _out206;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out207;
                (this).GenExpr((_235_indices).Select(_240_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out205, out _out206, out _out207);
                _241_idx = _out205;
                _242_idxOwned = _out206;
                _243_recIdentsIdx = _out207;
                _241_idx = RAST.__default.IntoUsize(_241_idx);
                r = RAST.Expr.create_SelectIndex(r, _241_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _243_recIdentsIdx);
              } else {
                RAST._IExpr _244_idx;
                DCOMP._IOwnership _245_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _246_recIdentsIdx;
                RAST._IExpr _out208;
                DCOMP._IOwnership _out209;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out210;
                (this).GenExpr((_235_indices).Select(_240_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out208, out _out209, out _out210);
                _244_idx = _out208;
                _245_idxOwned = _out209;
                _246_recIdentsIdx = _out210;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_244_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _246_recIdentsIdx);
              }
            }
            if (_239_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out211;
            DCOMP._IOwnership _out212;
            (this).FromOwned(r, expectedOwnership, out _out211, out _out212);
            r = _out211;
            resultingOwnership = _out212;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_IndexRange) {
          DAST._IExpression _247_on = _source0.dtor_expr;
          bool _248_isArray = _source0.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _249_low = _source0.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _250_high = _source0.dtor_high;
          {
            DCOMP._IOwnership _251_onExpectedOwnership;
            if (_248_isArray) {
              if (((this).ObjectType).is_RawPointers) {
                _251_onExpectedOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                _251_onExpectedOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              }
            } else {
              _251_onExpectedOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
            }
            RAST._IExpr _252_onExpr;
            DCOMP._IOwnership _253_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _254_recIdents;
            RAST._IExpr _out213;
            DCOMP._IOwnership _out214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out215;
            (this).GenExpr(_247_on, selfIdent, env, _251_onExpectedOwnership, out _out213, out _out214, out _out215);
            _252_onExpr = _out213;
            _253_onOwned = _out214;
            _254_recIdents = _out215;
            readIdents = _254_recIdents;
            Dafny.ISequence<Dafny.Rune> _255_methodName;
            if ((_249_low).is_Some) {
              if ((_250_high).is_Some) {
                _255_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice");
              } else {
                _255_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop");
              }
            } else if ((_250_high).is_Some) {
              _255_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take");
            } else {
              _255_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
            Dafny.ISequence<RAST._IExpr> _256_arguments;
            _256_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source3 = _249_low;
            {
              if (_source3.is_Some) {
                DAST._IExpression _257_l = _source3.dtor_value;
                {
                  RAST._IExpr _258_lExpr;
                  DCOMP._IOwnership _259___v201;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _260_recIdentsL;
                  RAST._IExpr _out216;
                  DCOMP._IOwnership _out217;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out218;
                  (this).GenExpr(_257_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out216, out _out217, out _out218);
                  _258_lExpr = _out216;
                  _259___v201 = _out217;
                  _260_recIdentsL = _out218;
                  _256_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_256_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_258_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _260_recIdentsL);
                }
                goto after_match3;
              }
            }
            {
            }
          after_match3: ;
            Std.Wrappers._IOption<DAST._IExpression> _source4 = _250_high;
            {
              if (_source4.is_Some) {
                DAST._IExpression _261_h = _source4.dtor_value;
                {
                  RAST._IExpr _262_hExpr;
                  DCOMP._IOwnership _263___v202;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _264_recIdentsH;
                  RAST._IExpr _out219;
                  DCOMP._IOwnership _out220;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out221;
                  (this).GenExpr(_261_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out219, out _out220, out _out221);
                  _262_hExpr = _out219;
                  _263___v202 = _out220;
                  _264_recIdentsH = _out221;
                  _256_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_256_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_262_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _264_recIdentsH);
                }
                goto after_match4;
              }
            }
            {
            }
          after_match4: ;
            r = _252_onExpr;
            if (_248_isArray) {
              if (!(_255_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _255_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _255_methodName);
              }
              Dafny.ISequence<Dafny.Rune> _265_object__suffix;
              if (((this).ObjectType).is_RawPointers) {
                _265_object__suffix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              } else {
                _265_object__suffix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_object");
              }
              r = ((RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _255_methodName), _265_object__suffix))).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_252_onExpr), _256_arguments));
            } else {
              if (!(_255_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_255_methodName)).Apply(_256_arguments);
              } else {
                r = (r).Clone();
              }
            }
            RAST._IExpr _out222;
            DCOMP._IOwnership _out223;
            (this).FromOwned(r, expectedOwnership, out _out222, out _out223);
            r = _out222;
            resultingOwnership = _out223;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TupleSelect) {
          DAST._IExpression _266_on = _source0.dtor_expr;
          BigInteger _267_idx = _source0.dtor_index;
          DAST._IType _268_fieldType = _source0.dtor_fieldType;
          {
            RAST._IExpr _269_onExpr;
            DCOMP._IOwnership _270_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _271_recIdents;
            RAST._IExpr _out224;
            DCOMP._IOwnership _out225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out226;
            (this).GenExpr(_266_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out224, out _out225, out _out226);
            _269_onExpr = _out224;
            _270_onOwnership = _out225;
            _271_recIdents = _out226;
            Dafny.ISequence<Dafny.Rune> _272_selName;
            _272_selName = Std.Strings.__default.OfNat(_267_idx);
            DAST._IType _source5 = _268_fieldType;
            {
              if (_source5.is_Tuple) {
                Dafny.ISequence<DAST._IType> _273_tps = _source5.dtor_Tuple_a0;
                if (((_268_fieldType).is_Tuple) && ((new BigInteger((_273_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _272_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _272_selName);
                }
                goto after_match5;
              }
            }
            {
            }
          after_match5: ;
            r = ((_269_onExpr).Sel(_272_selName)).Clone();
            RAST._IExpr _out227;
            DCOMP._IOwnership _out228;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out227, out _out228);
            r = _out227;
            resultingOwnership = _out228;
            readIdents = _271_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Call) {
          DAST._IExpression _274_on = _source0.dtor_on;
          DAST._ICallName _275_name = _source0.dtor_callName;
          Dafny.ISequence<DAST._IType> _276_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _277_args = _source0.dtor_args;
          {
            Dafny.ISequence<RAST._IExpr> _278_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _279_recIdents;
            Dafny.ISequence<RAST._IType> _280_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _281_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
            Dafny.ISequence<RAST._IType> _out231;
            Std.Wrappers._IOption<DAST._IResolvedType> _out232;
            (this).GenArgs(selfIdent, _275_name, _276_typeArgs, _277_args, env, out _out229, out _out230, out _out231, out _out232);
            _278_argExprs = _out229;
            _279_recIdents = _out230;
            _280_typeExprs = _out231;
            _281_fullNameQualifier = _out232;
            readIdents = _279_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source6 = _281_fullNameQualifier;
            {
              if (_source6.is_Some) {
                DAST._IResolvedType value0 = _source6.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _282_path = value0.dtor_path;
                Dafny.ISequence<DAST._IType> _283_onTypeArgs = value0.dtor_typeArgs;
                DAST._IResolvedTypeBase _284_base = value0.dtor_kind;
                RAST._IExpr _285_fullPath;
                RAST._IExpr _out233;
                _out233 = DCOMP.COMP.GenPathExpr(_282_path, true);
                _285_fullPath = _out233;
                Dafny.ISequence<RAST._IType> _286_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out234;
                _out234 = (this).GenTypeArgs(_283_onTypeArgs, DCOMP.GenTypeContext.@default());
                _286_onTypeExprs = _out234;
                RAST._IExpr _287_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _288_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _289_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_284_base).is_Trait) || ((_284_base).is_Class)) {
                  RAST._IExpr _out235;
                  DCOMP._IOwnership _out236;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out237;
                  (this).GenExpr(_274_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out235, out _out236, out _out237);
                  _287_onExpr = _out235;
                  _288_recOwnership = _out236;
                  _289_recIdents = _out237;
                  if (((this).ObjectType).is_RawPointers) {
                    _287_onExpr = ((this).read__macro).Apply1(_287_onExpr);
                  } else {
                    _287_onExpr = ((this).modify__macro).Apply1(_287_onExpr);
                  }
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _289_recIdents);
                } else {
                  DCOMP._IOwnership _290_expectedOnOwnership;
                  if (((this).ObjectType).is_RawPointers) {
                    _290_expectedOnOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
                  } else {
                    _290_expectedOnOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
                  }
                  RAST._IExpr _out238;
                  DCOMP._IOwnership _out239;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
                  (this).GenExpr(_274_on, selfIdent, env, _290_expectedOnOwnership, out _out238, out _out239, out _out240);
                  _287_onExpr = _out238;
                  _288_recOwnership = _out239;
                  _289_recIdents = _out240;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _289_recIdents);
                }
                r = ((((_285_fullPath).ApplyType(_286_onTypeExprs)).FSel(DCOMP.__default.escapeName((_275_name).dtor_name))).ApplyType(_280_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_287_onExpr), _278_argExprs));
                RAST._IExpr _out241;
                DCOMP._IOwnership _out242;
                (this).FromOwned(r, expectedOwnership, out _out241, out _out242);
                r = _out241;
                resultingOwnership = _out242;
                goto after_match6;
              }
            }
            {
              RAST._IExpr _291_onExpr;
              DCOMP._IOwnership _292___v208;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _293_recIdents;
              RAST._IExpr _out243;
              DCOMP._IOwnership _out244;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
              (this).GenExpr(_274_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out243, out _out244, out _out245);
              _291_onExpr = _out243;
              _292___v208 = _out244;
              _293_recIdents = _out245;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _293_recIdents);
              Dafny.ISequence<Dafny.Rune> _294_renderedName;
              _294_renderedName = (this).GetMethodName(_274_on, _275_name);
              DAST._IExpression _source7 = _274_on;
              {
                bool disjunctiveMatch0 = false;
                if (_source7.is_Companion) {
                  disjunctiveMatch0 = true;
                }
                if (_source7.is_ExternCompanion) {
                  disjunctiveMatch0 = true;
                }
                if (disjunctiveMatch0) {
                  {
                    _291_onExpr = (_291_onExpr).FSel(_294_renderedName);
                  }
                  goto after_match7;
                }
              }
              {
                {
                  if (!object.Equals(_291_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source8 = _275_name;
                    {
                      if (_source8.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source8.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _295_tpe = onType0.dtor_value;
                          RAST._IType _296_typ;
                          RAST._IType _out246;
                          _out246 = (this).GenType(_295_tpe, DCOMP.GenTypeContext.@default());
                          _296_typ = _out246;
                          if ((_296_typ).IsObjectOrPointer()) {
                            if (((this).ObjectType).is_RawPointers) {
                              _291_onExpr = ((this).read__macro).Apply1(_291_onExpr);
                            } else {
                              _291_onExpr = ((this).modify__macro).Apply1(_291_onExpr);
                            }
                          }
                          goto after_match8;
                        }
                      }
                    }
                    {
                    }
                  after_match8: ;
                  }
                  _291_onExpr = (_291_onExpr).Sel(_294_renderedName);
                }
              }
            after_match7: ;
              r = ((_291_onExpr).ApplyType(_280_typeExprs)).Apply(_278_argExprs);
              RAST._IExpr _out247;
              DCOMP._IOwnership _out248;
              (this).FromOwned(r, expectedOwnership, out _out247, out _out248);
              r = _out247;
              resultingOwnership = _out248;
              return ;
            }
          after_match6: ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _297_paramsDafny = _source0.dtor_params;
          DAST._IType _298_retType = _source0.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _299_body = _source0.dtor_body;
          {
            Dafny.ISequence<RAST._IFormal> _300_params;
            Dafny.ISequence<RAST._IFormal> _out249;
            _out249 = (this).GenParams(_297_paramsDafny, true);
            _300_params = _out249;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _301_paramNames;
            _301_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _302_paramTypesMap;
            _302_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi11 = new BigInteger((_300_params).Count);
            for (BigInteger _303_i = BigInteger.Zero; _303_i < _hi11; _303_i++) {
              Dafny.ISequence<Dafny.Rune> _304_name;
              _304_name = ((_300_params).Select(_303_i)).dtor_name;
              _301_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_301_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_304_name));
              _302_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_302_paramTypesMap, _304_name, ((_300_params).Select(_303_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _305_subEnv;
            _305_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_301_paramNames, _302_paramTypesMap));
            RAST._IExpr _306_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _307_recIdents;
            DCOMP._IEnvironment _308___v218;
            RAST._IExpr _out250;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out251;
            DCOMP._IEnvironment _out252;
            (this).GenStmts(_299_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _305_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out250, out _out251, out _out252);
            _306_recursiveGen = _out250;
            _307_recIdents = _out251;
            _308___v218 = _out252;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _307_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_307_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_309_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll0 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_0 in (_309_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _310_name = (Dafny.ISequence<Dafny.Rune>)_compr_0;
                if ((_309_paramNames).Contains(_310_name)) {
                  _coll0.Add(_310_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll0);
            }))())(_301_paramNames));
            RAST._IExpr _311_allReadCloned;
            _311_allReadCloned = (this).InitEmptyExpr();
            while (!(_307_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _312_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_307_recIdents).Elements) {
                _312_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
                if ((_307_recIdents).Contains(_312_next)) {
                  goto after__ASSIGN_SUCH_THAT_1;
                }
              }
              throw new System.Exception("assign-such-that search produced no value");
            after__ASSIGN_SUCH_THAT_1: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_312_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _313_selfCloned;
                DCOMP._IOwnership _314___v219;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _315___v220;
                RAST._IExpr _out253;
                DCOMP._IOwnership _out254;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out255;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out253, out _out254, out _out255);
                _313_selfCloned = _out253;
                _314___v219 = _out254;
                _315___v220 = _out255;
                _311_allReadCloned = (_311_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_313_selfCloned)));
              } else if (!((_301_paramNames).Contains(_312_next))) {
                RAST._IExpr _316_copy;
                _316_copy = (RAST.Expr.create_Identifier(_312_next)).Clone();
                _311_allReadCloned = (_311_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _312_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_316_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_312_next));
              }
              _307_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_307_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_312_next));
            }
            RAST._IType _317_retTypeGen;
            RAST._IType _out256;
            _out256 = (this).GenType(_298_retType, DCOMP.GenTypeContext.@default());
            _317_retTypeGen = _out256;
            r = RAST.Expr.create_Block((_311_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_300_params, Std.Wrappers.Option<RAST._IType>.create_Some(_317_retTypeGen), RAST.Expr.create_Block(_306_recursiveGen)))));
            RAST._IExpr _out257;
            DCOMP._IOwnership _out258;
            (this).FromOwned(r, expectedOwnership, out _out257, out _out258);
            r = _out257;
            resultingOwnership = _out258;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _318_values = _source0.dtor_values;
          DAST._IType _319_retType = _source0.dtor_retType;
          DAST._IExpression _320_expr = _source0.dtor_expr;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _321_paramNames;
            _321_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _322_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out259;
            _out259 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_323_value) => {
              return (_323_value).dtor__0;
            })), _318_values), false);
            _322_paramFormals = _out259;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _324_paramTypes;
            _324_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _325_paramNamesSet;
            _325_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi12 = new BigInteger((_318_values).Count);
            for (BigInteger _326_i = BigInteger.Zero; _326_i < _hi12; _326_i++) {
              Dafny.ISequence<Dafny.Rune> _327_name;
              _327_name = (((_318_values).Select(_326_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _328_rName;
              _328_rName = DCOMP.__default.escapeVar(_327_name);
              _321_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_321_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_328_rName));
              _324_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_324_paramTypes, _328_rName, ((_322_paramFormals).Select(_326_i)).dtor_tpe);
              _325_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_325_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_328_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (this).InitEmptyExpr();
            BigInteger _hi13 = new BigInteger((_318_values).Count);
            for (BigInteger _329_i = BigInteger.Zero; _329_i < _hi13; _329_i++) {
              RAST._IType _330_typeGen;
              RAST._IType _out260;
              _out260 = (this).GenType((((_318_values).Select(_329_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.@default());
              _330_typeGen = _out260;
              RAST._IExpr _331_valueGen;
              DCOMP._IOwnership _332___v221;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _333_recIdents;
              RAST._IExpr _out261;
              DCOMP._IOwnership _out262;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out263;
              (this).GenExpr(((_318_values).Select(_329_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out261, out _out262, out _out263);
              _331_valueGen = _out261;
              _332___v221 = _out262;
              _333_recIdents = _out263;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_318_values).Select(_329_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_330_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_331_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _333_recIdents);
            }
            DCOMP._IEnvironment _334_newEnv;
            _334_newEnv = DCOMP.Environment.create(_321_paramNames, _324_paramTypes);
            RAST._IExpr _335_recGen;
            DCOMP._IOwnership _336_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _337_recIdents;
            RAST._IExpr _out264;
            DCOMP._IOwnership _out265;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
            (this).GenExpr(_320_expr, selfIdent, _334_newEnv, expectedOwnership, out _out264, out _out265, out _out266);
            _335_recGen = _out264;
            _336_recOwned = _out265;
            _337_recIdents = _out266;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_337_recIdents, _325_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_335_recGen));
            RAST._IExpr _out267;
            DCOMP._IOwnership _out268;
            (this).FromOwnership(r, _336_recOwned, expectedOwnership, out _out267, out _out268);
            r = _out267;
            resultingOwnership = _out268;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _338_name = _source0.dtor_ident;
          DAST._IType _339_tpe = _source0.dtor_typ;
          DAST._IExpression _340_value = _source0.dtor_value;
          DAST._IExpression _341_iifeBody = _source0.dtor_iifeBody;
          {
            RAST._IExpr _342_valueGen;
            DCOMP._IOwnership _343___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _344_recIdents;
            RAST._IExpr _out269;
            DCOMP._IOwnership _out270;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
            (this).GenExpr(_340_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out269, out _out270, out _out271);
            _342_valueGen = _out269;
            _343___v222 = _out270;
            _344_recIdents = _out271;
            readIdents = _344_recIdents;
            RAST._IType _345_valueTypeGen;
            RAST._IType _out272;
            _out272 = (this).GenType(_339_tpe, DCOMP.GenTypeContext.@default());
            _345_valueTypeGen = _out272;
            Dafny.ISequence<Dafny.Rune> _346_iifeVar;
            _346_iifeVar = DCOMP.__default.escapeVar(_338_name);
            RAST._IExpr _347_bodyGen;
            DCOMP._IOwnership _348___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _349_bodyIdents;
            RAST._IExpr _out273;
            DCOMP._IOwnership _out274;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
            (this).GenExpr(_341_iifeBody, selfIdent, (env).AddAssigned(_346_iifeVar, _345_valueTypeGen), DCOMP.Ownership.create_OwnershipOwned(), out _out273, out _out274, out _out275);
            _347_bodyGen = _out273;
            _348___v223 = _out274;
            _349_bodyIdents = _out275;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_349_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_346_iifeVar)));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _346_iifeVar, Std.Wrappers.Option<RAST._IType>.create_Some(_345_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_342_valueGen))).Then(_347_bodyGen));
            RAST._IExpr _out276;
            DCOMP._IOwnership _out277;
            (this).FromOwned(r, expectedOwnership, out _out276, out _out277);
            r = _out276;
            resultingOwnership = _out277;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Apply) {
          DAST._IExpression _350_func = _source0.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _351_args = _source0.dtor_args;
          {
            RAST._IExpr _352_funcExpr;
            DCOMP._IOwnership _353___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _354_recIdents;
            RAST._IExpr _out278;
            DCOMP._IOwnership _out279;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
            (this).GenExpr(_350_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out278, out _out279, out _out280);
            _352_funcExpr = _out278;
            _353___v224 = _out279;
            _354_recIdents = _out280;
            readIdents = _354_recIdents;
            Dafny.ISequence<RAST._IExpr> _355_rArgs;
            _355_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi14 = new BigInteger((_351_args).Count);
            for (BigInteger _356_i = BigInteger.Zero; _356_i < _hi14; _356_i++) {
              RAST._IExpr _357_argExpr;
              DCOMP._IOwnership _358_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _359_argIdents;
              RAST._IExpr _out281;
              DCOMP._IOwnership _out282;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out283;
              (this).GenExpr((_351_args).Select(_356_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out281, out _out282, out _out283);
              _357_argExpr = _out281;
              _358_argOwned = _out282;
              _359_argIdents = _out283;
              _355_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_355_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_357_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _359_argIdents);
            }
            r = (_352_funcExpr).Apply(_355_rArgs);
            RAST._IExpr _out284;
            DCOMP._IOwnership _out285;
            (this).FromOwned(r, expectedOwnership, out _out284, out _out285);
            r = _out284;
            resultingOwnership = _out285;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TypeTest) {
          DAST._IExpression _360_on = _source0.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _361_dType = _source0.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _362_variant = _source0.dtor_variant;
          {
            RAST._IExpr _363_exprGen;
            DCOMP._IOwnership _364___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _365_recIdents;
            RAST._IExpr _out286;
            DCOMP._IOwnership _out287;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out288;
            (this).GenExpr(_360_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out286, out _out287, out _out288);
            _363_exprGen = _out286;
            _364___v225 = _out287;
            _365_recIdents = _out288;
            RAST._IExpr _366_variantExprPath;
            RAST._IExpr _out289;
            _out289 = DCOMP.COMP.GenPathExpr(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_361_dType, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_362_variant)), true);
            _366_variantExprPath = _out289;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_363_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0(), RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }"), _366_variantExprPath, DAST.Format.UnaryOpFormat.create_NoFormat())));
            RAST._IExpr _out290;
            DCOMP._IOwnership _out291;
            (this).FromOwned(r, expectedOwnership, out _out290, out _out291);
            r = _out290;
            resultingOwnership = _out291;
            readIdents = _365_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Is) {
          DAST._IExpression _367_expr = _source0.dtor_expr;
          DAST._IType _368_fromType = _source0.dtor_fromType;
          DAST._IType _369_toType = _source0.dtor_toType;
          {
            RAST._IExpr _370_expr;
            DCOMP._IOwnership _371_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _372_recIdents;
            RAST._IExpr _out292;
            DCOMP._IOwnership _out293;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
            (this).GenExpr(_367_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out292, out _out293, out _out294);
            _370_expr = _out292;
            _371_recOwned = _out293;
            _372_recIdents = _out294;
            RAST._IType _373_fromType;
            RAST._IType _out295;
            _out295 = (this).GenType(_368_fromType, DCOMP.GenTypeContext.@default());
            _373_fromType = _out295;
            RAST._IType _374_toType;
            RAST._IType _out296;
            _out296 = (this).GenType(_369_toType, DCOMP.GenTypeContext.@default());
            _374_toType = _out296;
            if (((_373_fromType).IsObjectOrPointer()) && ((_374_toType).IsObjectOrPointer())) {
              r = (((_370_expr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_374_toType).ObjectOrPointerUnderlying()))).Apply0();
            } else {
              RAST._IExpr _out297;
              _out297 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object or Ptr"), (this).InitEmptyExpr());
              r = _out297;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out298;
            DCOMP._IOwnership _out299;
            (this).FromOwnership(r, _371_recOwned, expectedOwnership, out _out298, out _out299);
            r = _out298;
            resultingOwnership = _out299;
            readIdents = _372_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_BoolBoundedPool) {
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out300;
            DCOMP._IOwnership _out301;
            (this).FromOwned(r, expectedOwnership, out _out300, out _out301);
            r = _out300;
            resultingOwnership = _out301;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetBoundedPool) {
          DAST._IExpression _375_of = _source0.dtor_of;
          {
            RAST._IExpr _376_exprGen;
            DCOMP._IOwnership _377___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _378_recIdents;
            RAST._IExpr _out302;
            DCOMP._IOwnership _out303;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
            (this).GenExpr(_375_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out302, out _out303, out _out304);
            _376_exprGen = _out302;
            _377___v226 = _out303;
            _378_recIdents = _out304;
            r = ((_376_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply0();
            RAST._IExpr _out305;
            DCOMP._IOwnership _out306;
            (this).FromOwned(r, expectedOwnership, out _out305, out _out306);
            r = _out305;
            resultingOwnership = _out306;
            readIdents = _378_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqBoundedPool) {
          DAST._IExpression _379_of = _source0.dtor_of;
          bool _380_includeDuplicates = _source0.dtor_includeDuplicates;
          {
            RAST._IExpr _381_exprGen;
            DCOMP._IOwnership _382___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _383_recIdents;
            RAST._IExpr _out307;
            DCOMP._IOwnership _out308;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out309;
            (this).GenExpr(_379_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out307, out _out308, out _out309);
            _381_exprGen = _out307;
            _382___v227 = _out308;
            _383_recIdents = _out309;
            r = ((_381_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply0();
            if (!(_380_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).AsExpr()).Apply1(r);
            }
            RAST._IExpr _out310;
            DCOMP._IOwnership _out311;
            (this).FromOwned(r, expectedOwnership, out _out310, out _out311);
            r = _out310;
            resultingOwnership = _out311;
            readIdents = _383_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapBoundedPool) {
          DAST._IExpression _384_of = _source0.dtor_of;
          {
            RAST._IExpr _385_exprGen;
            DCOMP._IOwnership _386___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _387_recIdents;
            RAST._IExpr _out312;
            DCOMP._IOwnership _out313;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
            (this).GenExpr(_384_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out312, out _out313, out _out314);
            _385_exprGen = _out312;
            _386___v228 = _out313;
            _387_recIdents = _out314;
            r = ((((_385_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply0();
            readIdents = _387_recIdents;
            RAST._IExpr _out315;
            DCOMP._IOwnership _out316;
            (this).FromOwned(r, expectedOwnership, out _out315, out _out316);
            r = _out315;
            resultingOwnership = _out316;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ExactBoundedPool) {
          DAST._IExpression _388_of = _source0.dtor_of;
          {
            RAST._IExpr _389_exprGen;
            DCOMP._IOwnership _390___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _391_recIdents;
            RAST._IExpr _out317;
            DCOMP._IOwnership _out318;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
            (this).GenExpr(_388_of, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out317, out _out318, out _out319);
            _389_exprGen = _out317;
            _390___v229 = _out318;
            _391_recIdents = _out319;
            r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("once"))).Apply1(_389_exprGen);
            readIdents = _391_recIdents;
            RAST._IExpr _out320;
            DCOMP._IOwnership _out321;
            (this).FromOwned(r, expectedOwnership, out _out320, out _out321);
            r = _out320;
            resultingOwnership = _out321;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_IntRange) {
          DAST._IType _392_typ = _source0.dtor_elemType;
          DAST._IExpression _393_lo = _source0.dtor_lo;
          DAST._IExpression _394_hi = _source0.dtor_hi;
          bool _395_up = _source0.dtor_up;
          {
            RAST._IExpr _396_lo;
            DCOMP._IOwnership _397___v230;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _398_recIdentsLo;
            RAST._IExpr _out322;
            DCOMP._IOwnership _out323;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
            (this).GenExpr(_393_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out322, out _out323, out _out324);
            _396_lo = _out322;
            _397___v230 = _out323;
            _398_recIdentsLo = _out324;
            RAST._IExpr _399_hi;
            DCOMP._IOwnership _400___v231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _401_recIdentsHi;
            RAST._IExpr _out325;
            DCOMP._IOwnership _out326;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
            (this).GenExpr(_394_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out325, out _out326, out _out327);
            _399_hi = _out325;
            _400___v231 = _out326;
            _401_recIdentsHi = _out327;
            if (_395_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_396_lo, _399_hi));
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_399_hi, _396_lo));
            }
            if (!((_392_typ).is_Primitive)) {
              RAST._IType _402_tpe;
              RAST._IType _out328;
              _out328 = (this).GenType(_392_typ, DCOMP.GenTypeContext.@default());
              _402_tpe = _out328;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map"))).Apply1((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_402_tpe))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into")));
            }
            RAST._IExpr _out329;
            DCOMP._IOwnership _out330;
            (this).FromOwned(r, expectedOwnership, out _out329, out _out330);
            r = _out329;
            resultingOwnership = _out330;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_398_recIdentsLo, _401_recIdentsHi);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_UnboundedIntRange) {
          DAST._IExpression _403_start = _source0.dtor_start;
          bool _404_up = _source0.dtor_up;
          {
            RAST._IExpr _405_start;
            DCOMP._IOwnership _406___v232;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _407_recIdentStart;
            RAST._IExpr _out331;
            DCOMP._IOwnership _out332;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out333;
            (this).GenExpr(_403_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out331, out _out332, out _out333);
            _405_start = _out331;
            _406___v232 = _out332;
            _407_recIdentStart = _out333;
            if (_404_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).AsExpr()).Apply1(_405_start);
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).AsExpr()).Apply1(_405_start);
            }
            RAST._IExpr _out334;
            DCOMP._IOwnership _out335;
            (this).FromOwned(r, expectedOwnership, out _out334, out _out335);
            r = _out334;
            resultingOwnership = _out335;
            readIdents = _407_recIdentStart;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapBuilder) {
          DAST._IType _408_keyType = _source0.dtor_keyType;
          DAST._IType _409_valueType = _source0.dtor_valueType;
          {
            RAST._IType _410_kType;
            RAST._IType _out336;
            _out336 = (this).GenType(_408_keyType, DCOMP.GenTypeContext.@default());
            _410_kType = _out336;
            RAST._IType _411_vType;
            RAST._IType _out337;
            _out337 = (this).GenType(_409_valueType, DCOMP.GenTypeContext.@default());
            _411_vType = _out337;
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_410_kType, _411_vType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply0();
            RAST._IExpr _out338;
            DCOMP._IOwnership _out339;
            (this).FromOwned(r, expectedOwnership, out _out338, out _out339);
            r = _out338;
            resultingOwnership = _out339;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetBuilder) {
          DAST._IType _412_elemType = _source0.dtor_elemType;
          {
            RAST._IType _413_eType;
            RAST._IType _out340;
            _out340 = (this).GenType(_412_elemType, DCOMP.GenTypeContext.@default());
            _413_eType = _out340;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_413_eType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply0();
            RAST._IExpr _out341;
            DCOMP._IOwnership _out342;
            (this).FromOwned(r, expectedOwnership, out _out341, out _out342);
            r = _out341;
            resultingOwnership = _out342;
            return ;
          }
          goto after_match0;
        }
      }
      {
        DAST._IType _414_elemType = _source0.dtor_elemType;
        DAST._IExpression _415_collection = _source0.dtor_collection;
        bool _416_is__forall = _source0.dtor_is__forall;
        DAST._IExpression _417_lambda = _source0.dtor_lambda;
        {
          RAST._IType _418_tpe;
          RAST._IType _out343;
          _out343 = (this).GenType(_414_elemType, DCOMP.GenTypeContext.@default());
          _418_tpe = _out343;
          RAST._IExpr _419_collectionGen;
          DCOMP._IOwnership _420___v233;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _421_recIdents;
          RAST._IExpr _out344;
          DCOMP._IOwnership _out345;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out346;
          (this).GenExpr(_415_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out344, out _out345, out _out346);
          _419_collectionGen = _out344;
          _420___v233 = _out345;
          _421_recIdents = _out346;
          Dafny.ISequence<DAST._IAttribute> _422_extraAttributes;
          _422_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if (((((_415_collection).is_IntRange) || ((_415_collection).is_UnboundedIntRange)) || ((_415_collection).is_SeqBoundedPool)) || ((_415_collection).is_ExactBoundedPool)) {
            _422_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_417_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _423_formals;
            _423_formals = (_417_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _424_newFormals;
            _424_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi15 = new BigInteger((_423_formals).Count);
            for (BigInteger _425_i = BigInteger.Zero; _425_i < _hi15; _425_i++) {
              var _pat_let_tv0 = _422_extraAttributes;
              var _pat_let_tv1 = _423_formals;
              _424_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_424_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_423_formals).Select(_425_i), _pat_let23_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let23_0, _426_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv0, ((_pat_let_tv1).Select(_425_i)).dtor_attributes), _pat_let24_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let24_0, _427_dt__update_hattributes_h0 => DAST.Formal.create((_426_dt__update__tmp_h0).dtor_name, (_426_dt__update__tmp_h0).dtor_typ, _427_dt__update_hattributes_h0)))))));
            }
            DAST._IExpression _428_newLambda;
            DAST._IExpression _429_dt__update__tmp_h1 = _417_lambda;
            Dafny.ISequence<DAST._IFormal> _430_dt__update_hparams_h0 = _424_newFormals;
            _428_newLambda = DAST.Expression.create_Lambda(_430_dt__update_hparams_h0, (_429_dt__update__tmp_h1).dtor_retType, (_429_dt__update__tmp_h1).dtor_body);
            RAST._IExpr _431_lambdaGen;
            DCOMP._IOwnership _432___v234;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _433_recLambdaIdents;
            RAST._IExpr _out347;
            DCOMP._IOwnership _out348;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
            (this).GenExpr(_428_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out347, out _out348, out _out349);
            _431_lambdaGen = _out347;
            _432___v234 = _out348;
            _433_recLambdaIdents = _out349;
            Dafny.ISequence<Dafny.Rune> _434_fn;
            if (_416_is__forall) {
              _434_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all");
            } else {
              _434_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any");
            }
            r = ((_419_collectionGen).Sel(_434_fn)).Apply1(((_431_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0());
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_421_recIdents, _433_recLambdaIdents);
          } else {
            RAST._IExpr _out350;
            _out350 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"), (this).InitEmptyExpr());
            r = _out350;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out351;
          DCOMP._IOwnership _out352;
          (this).FromOwned(r, expectedOwnership, out _out351, out _out352);
          r = _out351;
          resultingOwnership = _out352;
        }
      }
    after_match0: ;
    }
    public RAST._IExpr InitEmptyExpr() {
      return RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
    }
    public RAST._IExpr Error(Dafny.ISequence<Dafny.Rune> message, RAST._IExpr defaultExpr)
    {
      RAST._IExpr r = RAST.Expr.Default();
      if ((this.error).is_None) {
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(message);
      }
      r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/*"), message), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*/")), defaultExpr, DAST.Format.UnaryOpFormat.create_NoFormat());
      return r;
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> externalFiles)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      Dafny.ISequence<RAST._IModDecl> _0_externUseDecls;
      _0_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi0 = new BigInteger((externalFiles).Count);
      for (BigInteger _1_i = BigInteger.Zero; _1_i < _hi0; _1_i++) {
        Dafny.ISequence<Dafny.Rune> _2_externalFile;
        _2_externalFile = (externalFiles).Select(_1_i);
        Dafny.ISequence<Dafny.Rune> _3_externalMod;
        _3_externalMod = _2_externalFile;
        if (((new BigInteger((_2_externalFile).Count)) > (new BigInteger(3))) && (((_2_externalFile).Drop((new BigInteger((_2_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _3_externalMod = (_2_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _4_externMod;
        _4_externMod = RAST.Mod.create_ExternMod(_3_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_4_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _0_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_0_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.__default.crate).MSel(_3_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_0_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _0_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _5_allModules;
      _5_allModules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi1 = new BigInteger((p).Count);
      for (BigInteger _6_i = BigInteger.Zero; _6_i < _hi1; _6_i++) {
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _7_m;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out0;
        _out0 = (this).GenModule((p).Select(_6_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _7_m = _out0;
        _5_allModules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(_5_allModules, _7_m);
      }
      BigInteger _hi2 = new BigInteger(((_5_allModules).dtor_keys).Count);
      for (BigInteger _8_i = BigInteger.Zero; _8_i < _hi2; _8_i++) {
        if (!((_5_allModules).dtor_values).Contains(((_5_allModules).dtor_keys).Select(_8_i))) {
          goto continue_0;
        }
        RAST._IMod _9_m;
        _9_m = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_5_allModules).dtor_values,((_5_allModules).dtor_keys).Select(_8_i))).ToRust();
        BigInteger _hi3 = new BigInteger((this.optimizations).Count);
        for (BigInteger _10_j = BigInteger.Zero; _10_j < _hi3; _10_j++) {
          _9_m = Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>((this.optimizations).Select(_10_j))(_9_m);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_9_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < (new BigInteger((fullName).Count))) {
        if ((_0_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_0_i)));
        _0_i = (_0_i) + (BigInteger.One);
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
    public RAST._IType DafnyCharUnderlying { get {
      if ((this).UnicodeChars) {
        return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"));
      } else {
        return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16"));
      }
    } }
    public Dafny.ISequence<Dafny.Rune> string__of { get {
      if ((this).UnicodeChars) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_of");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_utf16_of");
      }
    } }
    public DCOMP._IObjectType _ObjectType {get; set;}
    public DCOMP._IObjectType ObjectType { get {
      return this._ObjectType;
    } }
    public Dafny.ISequence<Dafny.Rune> allocate { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("allocate");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("allocate_object");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> allocate__fn { get {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), (this).allocate);
    } }
    public Dafny.ISequence<Dafny.Rune> update__field__uninit__macro { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_uninit!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_uninit_object!");
      }
    } }
    public RAST._IExpr thisInConstructor { get {
      if (((this).ObjectType).is_RawPointers) {
        return RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
      } else {
        return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))).Clone();
      }
    } }
    public Dafny.ISequence<Dafny.Rune> array__construct { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("construct");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("construct_object");
      }
    } }
    public RAST._IExpr modify__macro { get {
      return ((RAST.__default.dafny__runtime).MSel(((((this).ObjectType).is_RawPointers) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("modify!")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("md!"))))).AsExpr();
    } }
    public RAST._IExpr read__macro { get {
      return ((RAST.__default.dafny__runtime).MSel(((((this).ObjectType).is_RawPointers) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read!")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rd!"))))).AsExpr();
    } }
    public Dafny.ISequence<Dafny.Rune> placebos__usize { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("placebos_usize");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("placebos_usize_object");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> update__field__if__uninit__macro { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_if_uninit!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_if_uninit_object!");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> Upcast { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Upcast");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastObject");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> UpcastFnMacro { get {
      return Dafny.Sequence<Dafny.Rune>.Concat((this).Upcast, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Fn!"));
    } }
    public Dafny.ISequence<Dafny.Rune> upcast { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_object");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> downcast { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cast!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cast_object!");
      }
    } }
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
    public static Dafny.ISequence<Dafny.Rune> TailRecursionPrefix { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_r");
    } }
    public static Dafny.ISequence<Dafny.Rune> DAFNY__EXTERN__MODULE { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_dafny_externs");
    } }
  }
} // end of namespace DCOMP