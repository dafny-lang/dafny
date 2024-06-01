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
      Dafny.ISequence<Dafny.Rune> _2219___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_2219___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _2219___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2219___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in115 = (i).Drop(new BigInteger(2));
        i = _in115;
        goto TAIL_CALL_START;
      } else {
        _2219___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2219___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in116 = (i).Drop(BigInteger.One);
        i = _in116;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _2220___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_2220___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _2220___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2220___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in117 = (i).Drop(BigInteger.One);
        i = _in117;
        goto TAIL_CALL_START;
      } else {
        _2220___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_2220___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
      } else if ((DCOMP.__default.reserved__rust).Contains(i)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), i);
      } else if (DCOMP.__default.is__idiomatic__rust__id(i)) {
        return DCOMP.__default.idiomatic__rust(i);
      } else if (DCOMP.__default.is__dafny__generated__id(i)) {
        return i;
      } else {
        Dafny.ISequence<Dafny.Rune> _2221_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _2221_r);
      }
    }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("async"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("await"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("const"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("else"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("enum"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ref"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("static"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("struct"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("union"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Keywords"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abstract"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("become"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("box"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("do"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("final"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("macro"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("override"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("priv"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("try"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("typeof"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsized"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("virtual"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("yield"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust__need__prefix { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128"));
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
    bool CanReadWithoutClone(Dafny.ISequence<Dafny.Rune> name);
    bool HasCloneSemantics(Dafny.ISequence<Dafny.Rune> name);
    Std.Wrappers._IOption<RAST._IType> GetType(Dafny.ISequence<Dafny.Rune> name);
    bool IsBorrowed(Dafny.ISequence<Dafny.Rune> name);
    bool IsBorrowedMut(Dafny.ISequence<Dafny.Rune> name);
    DCOMP._IEnvironment AddAssigned(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe);
    DCOMP._IEnvironment RemoveAssigned(Dafny.ISequence<Dafny.Rune> name);
  }
  public class Environment : _IEnvironment {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_names;
    public readonly Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _i_types;
    public Environment(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types) {
      this._i_names = names;
      this._i_types = types;
    }
    public _IEnvironment DowncastClone() {
      if (this is _IEnvironment dt) { return dt; }
      return new Environment(_i_names, _i_types);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Environment;
      return oth != null && object.Equals(this._i_names, oth._i_names) && object.Equals(this._i_types, oth._i_types);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_names));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_types));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Environment.Environment";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_names);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_types);
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
        return this._i_names;
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> dtor_types {
      get {
        return this._i_types;
      }
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
    public DCOMP._IEnvironment RemoveAssigned(Dafny.ISequence<Dafny.Rune> name) {
      BigInteger _2222_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _2222_indexInEnv), ((this).dtor_names).Drop((_2222_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
    }
  }

  public partial class COMP {
    public COMP() {
      this.error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.Default();
      this._i_UnicodeChars = false;
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> error {get; set;}
    public void __ctor(bool unicodeChars)
    {
      (this)._i_UnicodeChars = unicodeChars;
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
    }
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<Dafny.Rune> _2223_modName;
      _2223_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_2223_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _2224_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _2224_body = _out15;
        s = RAST.Mod.create_Mod(_2223_modName, _2224_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _2225_i = BigInteger.Zero; _2225_i < _hi5; _2225_i++) {
        Dafny.ISequence<RAST._IModDecl> _2226_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source69 = (body).Select(_2225_i);
        if (_source69.is_Module) {
          DAST._IModule _2227___mcc_h0 = _source69.dtor_Module_i_a0;
          DAST._IModule _2228_m = _2227___mcc_h0;
          RAST._IMod _2229_mm;
          RAST._IMod _out16;
          _out16 = (this).GenModule(_2228_m, containingPath);
          _2229_mm = _out16;
          _2226_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_2229_mm));
        } else if (_source69.is_Class) {
          DAST._IClass _2230___mcc_h1 = _source69.dtor_Class_i_a0;
          DAST._IClass _2231_c = _2230___mcc_h1;
          Dafny.ISequence<RAST._IModDecl> _out17;
          _out17 = (this).GenClass(_2231_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2231_c).dtor_name)));
          _2226_generated = _out17;
        } else if (_source69.is_Trait) {
          DAST._ITrait _2232___mcc_h2 = _source69.dtor_Trait_i_a0;
          DAST._ITrait _2233_t = _2232___mcc_h2;
          Dafny.ISequence<Dafny.Rune> _2234_tt;
          Dafny.ISequence<Dafny.Rune> _out18;
          _out18 = (this).GenTrait(_2233_t, containingPath);
          _2234_tt = _out18;
          _2226_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_RawDecl(_2234_tt));
        } else if (_source69.is_Newtype) {
          DAST._INewtype _2235___mcc_h3 = _source69.dtor_Newtype_i_a0;
          DAST._INewtype _2236_n = _2235___mcc_h3;
          Dafny.ISequence<RAST._IModDecl> _out19;
          _out19 = (this).GenNewtype(_2236_n);
          _2226_generated = _out19;
        } else {
          DAST._IDatatype _2237___mcc_h4 = _source69.dtor_Datatype_i_a0;
          DAST._IDatatype _2238_d = _2237___mcc_h4;
          Dafny.ISequence<RAST._IModDecl> _out20;
          _out20 = (this).GenDatatype(_2238_d);
          _2226_generated = _out20;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _2226_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _2239_genTpConstraint;
      _2239_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _2239_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_2239_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _2239_genTpConstraint);
    }
    public void GenTypeParameters(Dafny.ISequence<DAST._ITypeArgDecl> @params, out Dafny.ISet<DAST._IType> typeParamsSet, out Dafny.ISequence<RAST._IType> typeParams, out Dafny.ISequence<RAST._ITypeParamDecl> constrainedTypeParams, out Dafny.ISequence<Dafny.Rune> whereConstraints)
    {
      typeParamsSet = Dafny.Set<DAST._IType>.Empty;
      typeParams = Dafny.Sequence<RAST._IType>.Empty;
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Empty;
      whereConstraints = Dafny.Sequence<Dafny.Rune>.Empty;
      typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      whereConstraints = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger((@params).Count)).Sign == 1) {
        BigInteger _hi6 = new BigInteger((@params).Count);
        for (BigInteger _2240_tpI = BigInteger.Zero; _2240_tpI < _hi6; _2240_tpI++) {
          DAST._ITypeArgDecl _2241_tp;
          _2241_tp = (@params).Select(_2240_tpI);
          DAST._IType _2242_typeArg;
          RAST._ITypeParamDecl _2243_typeParam;
          DAST._IType _out21;
          RAST._ITypeParamDecl _out22;
          (this).GenTypeParam(_2241_tp, out _out21, out _out22);
          _2242_typeArg = _out21;
          _2243_typeParam = _out22;
          RAST._IType _2244_rType;
          RAST._IType _out23;
          _out23 = (this).GenType(_2242_typeArg, false, false);
          _2244_rType = _out23;
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_2242_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_2244_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2243_typeParam));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2245_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2246_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2247_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2248_whereConstraints;
      Dafny.ISet<DAST._IType> _out24;
      Dafny.ISequence<RAST._IType> _out25;
      Dafny.ISequence<RAST._ITypeParamDecl> _out26;
      Dafny.ISequence<Dafny.Rune> _out27;
      (this).GenTypeParameters((c).dtor_typeParams, out _out24, out _out25, out _out26, out _out27);
      _2245_typeParamsSet = _out24;
      _2246_rTypeParams = _out25;
      _2247_rTypeParamsDecls = _out26;
      _2248_whereConstraints = _out27;
      Dafny.ISequence<Dafny.Rune> _2249_constrainedTypeParams;
      _2249_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2247_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _2250_fields;
      _2250_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _2251_fieldInits;
      _2251_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _2252_fieldI = BigInteger.Zero; _2252_fieldI < _hi7; _2252_fieldI++) {
        DAST._IField _2253_field;
        _2253_field = ((c).dtor_fields).Select(_2252_fieldI);
        RAST._IType _2254_fieldType;
        RAST._IType _out28;
        _out28 = (this).GenType(((_2253_field).dtor_formal).dtor_typ, false, false);
        _2254_fieldType = _out28;
        Dafny.ISequence<Dafny.Rune> _2255_fieldRustName;
        _2255_fieldRustName = DCOMP.__default.escapeName(((_2253_field).dtor_formal).dtor_name);
        _2250_fields = Dafny.Sequence<RAST._IField>.Concat(_2250_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_2255_fieldRustName, _2254_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source70 = (_2253_field).dtor_defaultValue;
        if (_source70.is_None) {
          {
            RAST._IExpr _2256_default;
            _2256_default = RAST.__default.std__Default__default;
            _2251_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2251_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_2255_fieldRustName, _2256_default)));
          }
        } else {
          DAST._IExpression _2257___mcc_h0 = _source70.dtor_value;
          DAST._IExpression _2258_e = _2257___mcc_h0;
          {
            RAST._IExpr _2259_expr;
            DCOMP._IOwnership _2260___v39;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2261___v40;
            RAST._IExpr _out29;
            DCOMP._IOwnership _out30;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out31;
            (this).GenExpr(_2258_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out29, out _out30, out _out31);
            _2259_expr = _out29;
            _2260___v39 = _out30;
            _2261___v40 = _out31;
            _2251_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2251_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_2253_field).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cell::RefCell::new("), (_2259_expr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))))));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _2262_typeParamI = BigInteger.Zero; _2262_typeParamI < _hi8; _2262_typeParamI++) {
        DAST._IType _2263_typeArg;
        RAST._ITypeParamDecl _2264_typeParam;
        DAST._IType _out32;
        RAST._ITypeParamDecl _out33;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_2262_typeParamI), out _out32, out _out33);
        _2263_typeArg = _out32;
        _2264_typeParam = _out33;
        RAST._IType _2265_rTypeArg;
        RAST._IType _out34;
        _out34 = (this).GenType(_2263_typeArg, false, false);
        _2265_rTypeArg = _out34;
        _2250_fields = Dafny.Sequence<RAST._IField>.Concat(_2250_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_2262_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_2265_rTypeArg))))));
        _2251_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2251_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_2262_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _2266_datatypeName;
      _2266_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _2267_struct;
      _2267_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _2266_datatypeName, _2247_rTypeParamsDecls, RAST.Fields.create_NamedFields(_2250_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_2267_struct));
      Dafny.ISequence<RAST._IImplMember> _2268_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2269_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out35;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out36;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(path, (c).dtor_attributes))), _2245_typeParamsSet, out _out35, out _out36);
      _2268_implBodyRaw = _out35;
      _2269_traitBodies = _out36;
      Dafny.ISequence<RAST._IImplMember> _2270_implBody;
      _2270_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(RAST.Expr.create_Identifier(_2266_datatypeName), _2251_fieldInits))))), _2268_implBodyRaw);
      RAST._IImpl _2271_i;
      _2271_i = RAST.Impl.create_Impl(_2247_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2266_datatypeName), _2246_rTypeParams), _2248_whereConstraints, _2270_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2271_i)));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _2272_i;
        _2272_i = BigInteger.Zero;
        while ((_2272_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _2273_superClass;
          _2273_superClass = ((c).dtor_superClasses).Select(_2272_i);
          DAST._IType _source71 = _2273_superClass;
          if (_source71.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2274___mcc_h1 = _source71.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2275___mcc_h2 = _source71.dtor_typeArgs;
            DAST._IResolvedType _2276___mcc_h3 = _source71.dtor_resolved;
            DAST._IResolvedType _source72 = _2276___mcc_h3;
            if (_source72.is_Datatype) {
              DAST._IDatatypeType _2277___mcc_h7 = _source72.dtor_datatypeType;
            } else if (_source72.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2278___mcc_h9 = _source72.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _2279___mcc_h10 = _source72.dtor_attributes;
              Dafny.ISequence<DAST._IType> _2280_typeArgs = _2275___mcc_h2;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2281_traitPath = _2274___mcc_h1;
              {
                RAST._IType _2282_pathStr;
                RAST._IType _out37;
                _out37 = DCOMP.COMP.GenPath(_2281_traitPath);
                _2282_pathStr = _out37;
                Dafny.ISequence<RAST._IType> _2283_typeArgs;
                Dafny.ISequence<RAST._IType> _out38;
                _out38 = (this).GenTypeArgs(_2280_typeArgs, false, false);
                _2283_typeArgs = _out38;
                Dafny.ISequence<RAST._IImplMember> _2284_body;
                _2284_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_2269_traitBodies).Contains(_2281_traitPath)) {
                  _2284_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_2269_traitBodies,_2281_traitPath);
                }
                RAST._IType _2285_genSelfPath;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(path);
                _2285_genSelfPath = _out39;
                RAST._IModDecl _2286_x;
                _2286_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2247_rTypeParamsDecls, RAST.Type.create_TypeApp(_2282_pathStr, _2283_typeArgs), RAST.__default.Rc(RAST.Type.create_TypeApp(_2285_genSelfPath, _2246_rTypeParams)), _2248_whereConstraints, _2284_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_2286_x));
              }
            } else {
              DAST._IType _2287___mcc_h13 = _source72.dtor_baseType;
              DAST._INewtypeRange _2288___mcc_h14 = _source72.dtor_range;
              bool _2289___mcc_h15 = _source72.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _2290___mcc_h16 = _source72.dtor_attributes;
            }
          } else if (_source71.is_Nullable) {
            DAST._IType _2291___mcc_h21 = _source71.dtor_Nullable_i_a0;
          } else if (_source71.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2292___mcc_h23 = _source71.dtor_Tuple_i_a0;
          } else if (_source71.is_Array) {
            DAST._IType _2293___mcc_h25 = _source71.dtor_element;
            BigInteger _2294___mcc_h26 = _source71.dtor_dims;
          } else if (_source71.is_Seq) {
            DAST._IType _2295___mcc_h29 = _source71.dtor_element;
          } else if (_source71.is_Set) {
            DAST._IType _2296___mcc_h31 = _source71.dtor_element;
          } else if (_source71.is_Multiset) {
            DAST._IType _2297___mcc_h33 = _source71.dtor_element;
          } else if (_source71.is_Map) {
            DAST._IType _2298___mcc_h35 = _source71.dtor_key;
            DAST._IType _2299___mcc_h36 = _source71.dtor_value;
          } else if (_source71.is_SetBuilder) {
            DAST._IType _2300___mcc_h39 = _source71.dtor_element;
          } else if (_source71.is_MapBuilder) {
            DAST._IType _2301___mcc_h41 = _source71.dtor_key;
            DAST._IType _2302___mcc_h42 = _source71.dtor_value;
          } else if (_source71.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2303___mcc_h45 = _source71.dtor_args;
            DAST._IType _2304___mcc_h46 = _source71.dtor_result;
          } else if (_source71.is_Primitive) {
            DAST._IPrimitive _2305___mcc_h49 = _source71.dtor_Primitive_i_a0;
          } else if (_source71.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2306___mcc_h51 = _source71.dtor_Passthrough_i_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _2307___mcc_h53 = _source71.dtor_TypeArg_i_a0;
          }
          _2272_i = (_2272_i) + (BigInteger.One);
        }
      }
      RAST._IImpl _2308_d;
      _2308_d = RAST.Impl.create_ImplFor(_2247_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2266_datatypeName), _2246_rTypeParams), _2248_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(_2266_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()"))))))));
      Dafny.ISequence<RAST._IModDecl> _2309_defaultImpl;
      _2309_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2308_d));
      RAST._IImpl _2310_p;
      _2310_p = RAST.Impl.create_ImplFor(_2247_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2266_datatypeName), _2246_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), DCOMP.__default.escapeName(((c).dtor_enclosingModule))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"))))))));
      Dafny.ISequence<RAST._IModDecl> _2311_printImpl;
      _2311_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2310_p));
      RAST._IImpl _2312_pp;
      _2312_pp = RAST.Impl.create_ImplFor(_2247_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::cmp::PartialEq")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2266_datatypeName), _2246_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)")))))));
      Dafny.ISequence<RAST._IModDecl> _2313_ptrPartialEqImpl;
      _2313_ptrPartialEqImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_2312_pp));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(s, _2309_defaultImpl), _2311_printImpl), _2313_ptrPartialEqImpl);
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _2314_typeParamsSet;
      _2314_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _2315_typeParamDecls;
      _2315_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _2316_typeParams;
      _2316_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _2317_tpI;
      _2317_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        while ((_2317_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._ITypeArgDecl _2318_tp;
          _2318_tp = ((t).dtor_typeParams).Select(_2317_tpI);
          DAST._IType _2319_typeArg;
          RAST._ITypeParamDecl _2320_typeParamDecl;
          DAST._IType _out40;
          RAST._ITypeParamDecl _out41;
          (this).GenTypeParam(_2318_tp, out _out40, out _out41);
          _2319_typeArg = _out40;
          _2320_typeParamDecl = _out41;
          _2314_typeParamsSet = Dafny.Set<DAST._IType>.Union(_2314_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_2319_typeArg));
          _2315_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_2315_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2320_typeParamDecl));
          RAST._IType _2321_typeParam;
          RAST._IType _out42;
          _out42 = (this).GenType(_2319_typeArg, false, false);
          _2321_typeParam = _out42;
          _2316_typeParams = Dafny.Sequence<RAST._IType>.Concat(_2316_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_2321_typeParam));
          _2317_tpI = (_2317_tpI) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2322_fullPath;
      _2322_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _2323_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2324___v44;
      Dafny.ISequence<RAST._IImplMember> _out43;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out44;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_2322_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_2322_fullPath, (t).dtor_attributes)), _2314_typeParamsSet, out _out43, out _out44);
      _2323_implBody = _out43;
      _2324___v44 = _out44;
      s = (RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_2315_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _2316_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _2323_implBody)))._ToString(DCOMP.__default.IND);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2325_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2326_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2327_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2328_whereConstraints;
      Dafny.ISet<DAST._IType> _out45;
      Dafny.ISequence<RAST._IType> _out46;
      Dafny.ISequence<RAST._ITypeParamDecl> _out47;
      Dafny.ISequence<Dafny.Rune> _out48;
      (this).GenTypeParameters((c).dtor_typeParams, out _out45, out _out46, out _out47, out _out48);
      _2325_typeParamsSet = _out45;
      _2326_rTypeParams = _out46;
      _2327_rTypeParamsDecls = _out47;
      _2328_whereConstraints = _out48;
      Dafny.ISequence<Dafny.Rune> _2329_constrainedTypeParams;
      _2329_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2327_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _2330_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source73 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      if (_source73.is_None) {
        RAST._IType _out49;
        _out49 = (this).GenType((c).dtor_base, false, false);
        _2330_underlyingType = _out49;
      } else {
        RAST._IType _2331___mcc_h0 = _source73.dtor_value;
        RAST._IType _2332_v = _2331___mcc_h0;
        _2330_underlyingType = _2332_v;
      }
      DAST._IType _2333_resultingType;
      _2333_resultingType = DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Newtype((c).dtor_base, (c).dtor_range, false, (c).dtor_attributes));
      Dafny.ISequence<Dafny.Rune> _2334_datatypeName;
      _2334_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _2334_datatypeName, _2327_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _2330_underlyingType))))));
      RAST._IExpr _2335_fnBody;
      _2335_fnBody = RAST.Expr.create_Identifier(_2334_datatypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source74 = (c).dtor_witnessExpr;
      if (_source74.is_None) {
        {
          _2335_fnBody = (_2335_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      } else {
        DAST._IExpression _2336___mcc_h1 = _source74.dtor_value;
        DAST._IExpression _2337_e = _2336___mcc_h1;
        {
          DAST._IExpression _2338_e;
          _2338_e = ((object.Equals((c).dtor_base, _2333_resultingType)) ? (_2337_e) : (DAST.Expression.create_Convert(_2337_e, (c).dtor_base, _2333_resultingType)));
          RAST._IExpr _2339_eStr;
          DCOMP._IOwnership _2340___v45;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2341___v46;
          RAST._IExpr _out50;
          DCOMP._IOwnership _out51;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out52;
          (this).GenExpr(_2338_e, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out50, out _out51, out _out52);
          _2339_eStr = _out50;
          _2340___v45 = _out51;
          _2341___v46 = _out52;
          _2335_fnBody = (_2335_fnBody).Apply1(_2339_eStr);
        }
      }
      RAST._IImplMember _2342_body;
      _2342_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2335_fnBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2327_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2334_datatypeName), _2326_rTypeParams), _2328_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_2342_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2327_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2334_datatypeName), _2326_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2327_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2334_datatypeName), _2326_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_2330_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISet<DAST._IType> _2343_typeParamsSet;
      Dafny.ISequence<RAST._IType> _2344_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2345_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _2346_whereConstraints;
      Dafny.ISet<DAST._IType> _out53;
      Dafny.ISequence<RAST._IType> _out54;
      Dafny.ISequence<RAST._ITypeParamDecl> _out55;
      Dafny.ISequence<Dafny.Rune> _out56;
      (this).GenTypeParameters((c).dtor_typeParams, out _out53, out _out54, out _out55, out _out56);
      _2343_typeParamsSet = _out53;
      _2344_rTypeParams = _out54;
      _2345_rTypeParamsDecls = _out55;
      _2346_whereConstraints = _out56;
      Dafny.ISequence<Dafny.Rune> _2347_datatypeName;
      _2347_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _2348_ctors;
      _2348_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2349_i = BigInteger.Zero; _2349_i < _hi9; _2349_i++) {
        DAST._IDatatypeCtor _2350_ctor;
        _2350_ctor = ((c).dtor_ctors).Select(_2349_i);
        Dafny.ISequence<RAST._IField> _2351_ctorArgs;
        _2351_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        BigInteger _hi10 = new BigInteger(((_2350_ctor).dtor_args).Count);
        for (BigInteger _2352_j = BigInteger.Zero; _2352_j < _hi10; _2352_j++) {
          DAST._IFormal _2353_formal;
          _2353_formal = ((_2350_ctor).dtor_args).Select(_2352_j);
          RAST._IType _2354_formalType;
          RAST._IType _out57;
          _out57 = (this).GenType((_2353_formal).dtor_typ, false, false);
          _2354_formalType = _out57;
          if ((c).dtor_isCo) {
            _2351_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_2351_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_2353_formal).dtor_name), RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_2354_formalType))))));
          } else {
            _2351_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_2351_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(DCOMP.__default.escapeName((_2353_formal).dtor_name), _2354_formalType))));
          }
        }
        _2348_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_2348_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_2350_ctor).dtor_name), RAST.Fields.create_NamedFields(_2351_ctorArgs))));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2355_selfPath;
      _2355_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _2356_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _2357_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out58;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out59;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(DAST.DatatypeType.create(_2355_selfPath, (c).dtor_attributes))), _2343_typeParamsSet, out _out58, out _out59);
      _2356_implBodyRaw = _out58;
      _2357_traitBodies = _out59;
      Dafny.ISequence<RAST._IImplMember> _2358_implBody;
      _2358_implBody = _2356_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2359_emittedFields;
      _2359_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi11 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2360_i = BigInteger.Zero; _2360_i < _hi11; _2360_i++) {
        DAST._IDatatypeCtor _2361_ctor;
        _2361_ctor = ((c).dtor_ctors).Select(_2360_i);
        BigInteger _hi12 = new BigInteger(((_2361_ctor).dtor_args).Count);
        for (BigInteger _2362_j = BigInteger.Zero; _2362_j < _hi12; _2362_j++) {
          DAST._IFormal _2363_formal;
          _2363_formal = ((_2361_ctor).dtor_args).Select(_2362_j);
          if (!((_2359_emittedFields).Contains((_2363_formal).dtor_name))) {
            _2359_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2359_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_2363_formal).dtor_name));
            RAST._IType _2364_formalType;
            RAST._IType _out60;
            _out60 = (this).GenType((_2363_formal).dtor_typ, false, false);
            _2364_formalType = _out60;
            Dafny.ISequence<RAST._IMatchCase> _2365_cases;
            _2365_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _2366_k = BigInteger.Zero; _2366_k < _hi13; _2366_k++) {
              DAST._IDatatypeCtor _2367_ctor2;
              _2367_ctor2 = ((c).dtor_ctors).Select(_2366_k);
              Dafny.ISequence<Dafny.Rune> _2368_pattern;
              _2368_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2347_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_2367_ctor2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              Dafny.ISequence<Dafny.Rune> _2369_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              bool _2370_hasMatchingField;
              _2370_hasMatchingField = false;
              BigInteger _hi14 = new BigInteger(((_2367_ctor2).dtor_args).Count);
              for (BigInteger _2371_l = BigInteger.Zero; _2371_l < _hi14; _2371_l++) {
                DAST._IFormal _2372_formal2;
                _2372_formal2 = ((_2367_ctor2).dtor_args).Select(_2371_l);
                if (object.Equals((_2363_formal).dtor_name, (_2372_formal2).dtor_name)) {
                  _2370_hasMatchingField = true;
                }
                _2368_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2368_pattern, DCOMP.__default.escapeName((_2372_formal2).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2368_pattern = Dafny.Sequence<Dafny.Rune>.Concat(_2368_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              if (_2370_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _2369_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), DCOMP.__default.escapeName((_2363_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _2369_rhs = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_2363_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _2369_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _2373_ctorMatch;
              _2373_ctorMatch = RAST.MatchCase.create(_2368_pattern, RAST.Expr.create_RawExpr(_2369_rhs));
              _2365_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2365_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_2373_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _2365_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2365_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_2347_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _2374_methodBody;
            _2374_methodBody = RAST.Expr.create_Match(RAST.__default.self, _2365_cases);
            _2358_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_2358_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(DCOMP.__default.escapeName((_2363_formal).dtor_name), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_2364_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2374_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _2375_types;
        _2375_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi15 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _2376_typeI = BigInteger.Zero; _2376_typeI < _hi15; _2376_typeI++) {
          DAST._IType _2377_typeArg;
          RAST._ITypeParamDecl _2378_rTypeParamDecl;
          DAST._IType _out61;
          RAST._ITypeParamDecl _out62;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_2376_typeI), out _out61, out _out62);
          _2377_typeArg = _out61;
          _2378_rTypeParamDecl = _out62;
          RAST._IType _2379_rTypeArg;
          RAST._IType _out63;
          _out63 = (this).GenType(_2377_typeArg, false, false);
          _2379_rTypeArg = _out63;
          _2375_types = Dafny.Sequence<RAST._IType>.Concat(_2375_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_2379_rTypeArg))));
        }
        _2348_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_2348_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_2380_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _2380_tpe);
})), _2375_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _2381_enumBody;
      _2381_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _2347_datatypeName, _2345_rTypeParamsDecls, _2348_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2345_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2347_datatypeName), _2344_rTypeParams), _2346_whereConstraints, _2358_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _2382_printImplBodyCases;
      _2382_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _2383_i = BigInteger.Zero; _2383_i < _hi16; _2383_i++) {
        DAST._IDatatypeCtor _2384_ctor;
        _2384_ctor = ((c).dtor_ctors).Select(_2383_i);
        Dafny.ISequence<Dafny.Rune> _2385_ctorMatch;
        _2385_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName((_2384_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _2386_modulePrefix;
        _2386_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.escapeName(((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _2387_ctorName;
        _2387_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2386_modulePrefix, DCOMP.__default.escapeName((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName((_2384_ctor).dtor_name));
        if (((new BigInteger((_2387_ctorName).Count)) >= (new BigInteger(13))) && (((_2387_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _2387_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _2388_printRhs;
        _2388_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _2387_ctorName), (((_2384_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        BigInteger _hi17 = new BigInteger(((_2384_ctor).dtor_args).Count);
        for (BigInteger _2389_j = BigInteger.Zero; _2389_j < _hi17; _2389_j++) {
          DAST._IFormal _2390_formal;
          _2390_formal = ((_2384_ctor).dtor_args).Select(_2389_j);
          Dafny.ISequence<Dafny.Rune> _2391_formalName;
          _2391_formalName = DCOMP.__default.escapeName((_2390_formal).dtor_name);
          _2385_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2385_ctorMatch, _2391_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_2389_j).Sign == 1) {
            _2388_printRhs = (_2388_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _2388_printRhs = (_2388_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), DCOMP.__default.escapeName((_2390_formal).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        _2385_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_2385_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_2384_ctor).dtor_hasAnyArgs) {
          _2388_printRhs = (_2388_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _2388_printRhs = (_2388_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _2382_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2382_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2347_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2385_ctorMatch), RAST.Expr.create_Block(_2388_printRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _2382_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_2382_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_2347_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _2392_defaultConstrainedTypeParams;
      _2392_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2345_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _2393_printImplBody;
      _2393_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _2382_printImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _2394_printImpl;
      _2394_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2345_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2347_datatypeName), _2344_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2345_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2347_datatypeName), _2344_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2393_printImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _2395_defaultImpl;
      _2395_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _2396_structName;
        _2396_structName = (RAST.Expr.create_Identifier(_2347_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _2397_structAssignments;
        _2397_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi18 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _2398_i = BigInteger.Zero; _2398_i < _hi18; _2398_i++) {
          DAST._IFormal _2399_formal;
          _2399_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_2398_i);
          _2397_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2397_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName((_2399_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _2400_defaultConstrainedTypeParams;
        _2400_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2345_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _2401_fullType;
        _2401_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_2347_datatypeName), _2344_rTypeParams);
        _2395_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2400_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _2401_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_2401_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_2396_structName, _2397_structAssignments))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_2381_enumBody, _2394_printImpl), _2395_defaultImpl);
      return s;
    }
    public static RAST._IType GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType r = RAST.Type.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        r = RAST.Type.create_SelfOwned();
        return r;
      } else {
        r = ((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) ? (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) : (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"))));
        BigInteger _hi19 = new BigInteger((p).Count);
        for (BigInteger _2402_i = BigInteger.Zero; _2402_i < _hi19; _2402_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_2402_i))));
        }
      }
      return r;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IExpr r = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        r = RAST.__default.self;
        return r;
      } else {
        r = ((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) ? (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) : (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"))));
        BigInteger _hi20 = new BigInteger((p).Count);
        for (BigInteger _2403_i = BigInteger.Zero; _2403_i < _hi20; _2403_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_2403_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger((args).Count)).Sign == 1) {
        BigInteger _2404_i;
        _2404_i = BigInteger.Zero;
        while ((_2404_i) < (new BigInteger((args).Count))) {
          RAST._IType _2405_genTp;
          RAST._IType _out64;
          _out64 = (this).GenType((args).Select(_2404_i), inBinding, inFn);
          _2405_genTp = _out64;
          s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_2405_genTp));
          _2404_i = (_2404_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public RAST._IType GenType(DAST._IType c, bool inBinding, bool inFn)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source75 = c;
      if (_source75.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2406___mcc_h0 = _source75.dtor_Path_i_a0;
        Dafny.ISequence<DAST._IType> _2407___mcc_h1 = _source75.dtor_typeArgs;
        DAST._IResolvedType _2408___mcc_h2 = _source75.dtor_resolved;
        DAST._IResolvedType _2409_resolved = _2408___mcc_h2;
        Dafny.ISequence<DAST._IType> _2410_args = _2407___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2411_p = _2406___mcc_h0;
        {
          RAST._IType _2412_t;
          RAST._IType _out65;
          _out65 = DCOMP.COMP.GenPath(_2411_p);
          _2412_t = _out65;
          Dafny.ISequence<RAST._IType> _2413_typeArgs;
          Dafny.ISequence<RAST._IType> _out66;
          _out66 = (this).GenTypeArgs(_2410_args, inBinding, inFn);
          _2413_typeArgs = _out66;
          s = RAST.Type.create_TypeApp(_2412_t, _2413_typeArgs);
          DAST._IResolvedType _source76 = _2409_resolved;
          if (_source76.is_Datatype) {
            DAST._IDatatypeType _2414___mcc_h21 = _source76.dtor_datatypeType;
            DAST._IDatatypeType _source77 = _2414___mcc_h21;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2415___mcc_h22 = _source77.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _2416___mcc_h23 = _source77.dtor_attributes;
            Dafny.ISequence<DAST._IAttribute> _2417_attributes = _2416___mcc_h23;
          } else if (_source76.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2418___mcc_h24 = _source76.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _2419___mcc_h25 = _source76.dtor_attributes;
            {
              if ((_2411_p).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
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
            DAST._IType _2420___mcc_h26 = _source76.dtor_baseType;
            DAST._INewtypeRange _2421___mcc_h27 = _source76.dtor_range;
            bool _2422___mcc_h28 = _source76.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _2423___mcc_h29 = _source76.dtor_attributes;
            Dafny.ISequence<DAST._IAttribute> _2424_attributes = _2423___mcc_h29;
            bool _2425_erased = _2422___mcc_h28;
            DAST._INewtypeRange _2426_range = _2421___mcc_h27;
            DAST._IType _2427_t = _2420___mcc_h26;
            {
              if (_2425_erased) {
                Std.Wrappers._IOption<RAST._IType> _source78 = DCOMP.COMP.NewtypeToRustType(_2427_t, _2426_range);
                if (_source78.is_None) {
                } else {
                  RAST._IType _2428___mcc_h30 = _source78.dtor_value;
                  RAST._IType _2429_v = _2428___mcc_h30;
                  s = _2429_v;
                }
              }
            }
          }
        }
      } else if (_source75.is_Nullable) {
        DAST._IType _2430___mcc_h3 = _source75.dtor_Nullable_i_a0;
        DAST._IType _2431_inner = _2430___mcc_h3;
        {
          RAST._IType _2432_innerExpr;
          RAST._IType _out67;
          _out67 = (this).GenType(_2431_inner, inBinding, inFn);
          _2432_innerExpr = _out67;
          s = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option")), Dafny.Sequence<RAST._IType>.FromElements(_2432_innerExpr));
        }
      } else if (_source75.is_Tuple) {
        Dafny.ISequence<DAST._IType> _2433___mcc_h4 = _source75.dtor_Tuple_i_a0;
        Dafny.ISequence<DAST._IType> _2434_types = _2433___mcc_h4;
        {
          Dafny.ISequence<RAST._IType> _2435_args;
          _2435_args = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2436_i;
          _2436_i = BigInteger.Zero;
          while ((_2436_i) < (new BigInteger((_2434_types).Count))) {
            RAST._IType _2437_generated;
            RAST._IType _out68;
            _out68 = (this).GenType((_2434_types).Select(_2436_i), inBinding, inFn);
            _2437_generated = _out68;
            _2435_args = Dafny.Sequence<RAST._IType>.Concat(_2435_args, Dafny.Sequence<RAST._IType>.FromElements(_2437_generated));
            _2436_i = (_2436_i) + (BigInteger.One);
          }
          s = (((new BigInteger((_2434_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_2435_args)) : (RAST.__default.SystemTupleType(_2435_args)));
        }
      } else if (_source75.is_Array) {
        DAST._IType _2438___mcc_h5 = _source75.dtor_element;
        BigInteger _2439___mcc_h6 = _source75.dtor_dims;
        BigInteger _2440_dims = _2439___mcc_h6;
        DAST._IType _2441_element = _2438___mcc_h5;
        {
          RAST._IType _2442_elem;
          RAST._IType _out69;
          _out69 = (this).GenType(_2441_element, inBinding, inFn);
          _2442_elem = _out69;
          s = _2442_elem;
          BigInteger _2443_i;
          _2443_i = BigInteger.Zero;
          while ((_2443_i) < (_2440_dims)) {
            s = RAST.__default.Rc(RAST.__default.RefCell(RAST.__default.Vec(s)));
            _2443_i = (_2443_i) + (BigInteger.One);
          }
        }
      } else if (_source75.is_Seq) {
        DAST._IType _2444___mcc_h7 = _source75.dtor_element;
        DAST._IType _2445_element = _2444___mcc_h7;
        {
          RAST._IType _2446_elem;
          RAST._IType _out70;
          _out70 = (this).GenType(_2445_element, inBinding, inFn);
          _2446_elem = _out70;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_2446_elem));
        }
      } else if (_source75.is_Set) {
        DAST._IType _2447___mcc_h8 = _source75.dtor_element;
        DAST._IType _2448_element = _2447___mcc_h8;
        {
          RAST._IType _2449_elem;
          RAST._IType _out71;
          _out71 = (this).GenType(_2448_element, inBinding, inFn);
          _2449_elem = _out71;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_2449_elem));
        }
      } else if (_source75.is_Multiset) {
        DAST._IType _2450___mcc_h9 = _source75.dtor_element;
        DAST._IType _2451_element = _2450___mcc_h9;
        {
          RAST._IType _2452_elem;
          RAST._IType _out72;
          _out72 = (this).GenType(_2451_element, inBinding, inFn);
          _2452_elem = _out72;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_2452_elem));
        }
      } else if (_source75.is_Map) {
        DAST._IType _2453___mcc_h10 = _source75.dtor_key;
        DAST._IType _2454___mcc_h11 = _source75.dtor_value;
        DAST._IType _2455_value = _2454___mcc_h11;
        DAST._IType _2456_key = _2453___mcc_h10;
        {
          RAST._IType _2457_keyType;
          RAST._IType _out73;
          _out73 = (this).GenType(_2456_key, inBinding, inFn);
          _2457_keyType = _out73;
          RAST._IType _2458_valueType;
          RAST._IType _out74;
          _out74 = (this).GenType(_2455_value, inBinding, inFn);
          _2458_valueType = _out74;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_2457_keyType, _2458_valueType));
        }
      } else if (_source75.is_SetBuilder) {
        DAST._IType _2459___mcc_h12 = _source75.dtor_element;
        DAST._IType _2460_elem = _2459___mcc_h12;
        {
          RAST._IType _2461_elemType;
          RAST._IType _out75;
          _out75 = (this).GenType(_2460_elem, inBinding, inFn);
          _2461_elemType = _out75;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2461_elemType));
        }
      } else if (_source75.is_MapBuilder) {
        DAST._IType _2462___mcc_h13 = _source75.dtor_key;
        DAST._IType _2463___mcc_h14 = _source75.dtor_value;
        DAST._IType _2464_value = _2463___mcc_h14;
        DAST._IType _2465_key = _2462___mcc_h13;
        {
          RAST._IType _2466_keyType;
          RAST._IType _out76;
          _out76 = (this).GenType(_2465_key, inBinding, inFn);
          _2466_keyType = _out76;
          RAST._IType _2467_valueType;
          RAST._IType _out77;
          _out77 = (this).GenType(_2464_value, inBinding, inFn);
          _2467_valueType = _out77;
          s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_2466_keyType, _2467_valueType));
        }
      } else if (_source75.is_Arrow) {
        Dafny.ISequence<DAST._IType> _2468___mcc_h15 = _source75.dtor_args;
        DAST._IType _2469___mcc_h16 = _source75.dtor_result;
        DAST._IType _2470_result = _2469___mcc_h16;
        Dafny.ISequence<DAST._IType> _2471_args = _2468___mcc_h15;
        {
          Dafny.ISequence<RAST._IType> _2472_argTypes;
          _2472_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _2473_i;
          _2473_i = BigInteger.Zero;
          while ((_2473_i) < (new BigInteger((_2471_args).Count))) {
            RAST._IType _2474_generated;
            RAST._IType _out78;
            _out78 = (this).GenType((_2471_args).Select(_2473_i), inBinding, true);
            _2474_generated = _out78;
            _2472_argTypes = Dafny.Sequence<RAST._IType>.Concat(_2472_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_2474_generated)));
            _2473_i = (_2473_i) + (BigInteger.One);
          }
          RAST._IType _2475_resultType;
          RAST._IType _out79;
          _out79 = (this).GenType(_2470_result, inBinding, (inFn) || (inBinding));
          _2475_resultType = _out79;
          s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_2472_argTypes, _2475_resultType)));
        }
      } else if (_source75.is_Primitive) {
        DAST._IPrimitive _2476___mcc_h17 = _source75.dtor_Primitive_i_a0;
        DAST._IPrimitive _2477_p = _2476___mcc_h17;
        {
          DAST._IPrimitive _source79 = _2477_p;
          if (_source79.is_Int) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
          } else if (_source79.is_Real) {
            s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
          } else if (_source79.is_String) {
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
          } else if (_source79.is_Bool) {
            s = RAST.Type.create_Bool();
          } else {
            s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
          }
        }
      } else if (_source75.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _2478___mcc_h18 = _source75.dtor_Passthrough_i_a0;
        Dafny.ISequence<Dafny.Rune> _2479_v = _2478___mcc_h18;
        s = RAST.__default.RawType(_2479_v);
      } else {
        Dafny.ISequence<Dafny.Rune> _2480___mcc_h19 = _source75.dtor_TypeArg_i_a0;
        Dafny.ISequence<Dafny.Rune> _source80 = _2480___mcc_h19;
        Dafny.ISequence<Dafny.Rune> _2481___mcc_h20 = _source80;
        Dafny.ISequence<Dafny.Rune> _2482_name = _2481___mcc_h20;
        s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_2482_name));
      }
      return s;
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _hi21 = new BigInteger((body).Count);
      for (BigInteger _2483_i = BigInteger.Zero; _2483_i < _hi21; _2483_i++) {
        DAST._IMethod _source81 = (body).Select(_2483_i);
        DAST._IMethod _2484___mcc_h0 = _source81;
        DAST._IMethod _2485_m = _2484___mcc_h0;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source82 = (_2485_m).dtor_overridingPath;
          if (_source82.is_None) {
            {
              RAST._IImplMember _2486_generated;
              RAST._IImplMember _out80;
              _out80 = (this).GenMethod(_2485_m, forTrait, enclosingType, enclosingTypeParams);
              _2486_generated = _out80;
              s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_2486_generated));
            }
          } else {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2487___mcc_h1 = _source82.dtor_value;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2488_p = _2487___mcc_h1;
            {
              Dafny.ISequence<RAST._IImplMember> _2489_existing;
              _2489_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
              if ((traitBodies).Contains(_2488_p)) {
                _2489_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_2488_p);
              }
              RAST._IImplMember _2490_genMethod;
              RAST._IImplMember _out81;
              _out81 = (this).GenMethod(_2485_m, true, enclosingType, enclosingTypeParams);
              _2490_genMethod = _out81;
              _2489_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_2489_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_2490_genMethod));
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_2488_p, _2489_existing)));
            }
          }
        }
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi22 = new BigInteger((@params).Count);
      for (BigInteger _2491_i = BigInteger.Zero; _2491_i < _hi22; _2491_i++) {
        DAST._IFormal _2492_param;
        _2492_param = (@params).Select(_2491_i);
        RAST._IType _2493_paramType;
        RAST._IType _out82;
        _out82 = (this).GenType((_2492_param).dtor_typ, false, false);
        _2493_paramType = _out82;
        if ((!((_2493_paramType).CanReadWithoutClone())) && (!((_2492_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _2493_paramType = RAST.Type.create_Borrowed(_2493_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_2492_param).dtor_name), _2493_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _2494_params;
      Dafny.ISequence<RAST._IFormal> _out83;
      _out83 = (this).GenParams((m).dtor_params);
      _2494_params = _out83;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2495_paramNames;
      _2495_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2496_paramTypes;
      _2496_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi23 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _2497_paramI = BigInteger.Zero; _2497_paramI < _hi23; _2497_paramI++) {
        DAST._IFormal _2498_dafny__formal;
        _2498_dafny__formal = ((m).dtor_params).Select(_2497_paramI);
        RAST._IFormal _2499_formal;
        _2499_formal = (_2494_params).Select(_2497_paramI);
        Dafny.ISequence<Dafny.Rune> _2500_name;
        _2500_name = (_2499_formal).dtor_name;
        _2495_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2495_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2500_name));
        _2496_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2496_paramTypes, _2500_name, (_2499_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _2501_fnName;
      _2501_fnName = DCOMP.__default.escapeName((m).dtor_name);
      Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2502_selfIdentifier;
      _2502_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _2503_selfId;
        _2503_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_2501_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _2503_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        if (forTrait) {
          RAST._IFormal _2504_selfFormal;
          _2504_selfFormal = RAST.Formal.selfBorrowedMut;
          _2494_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_2504_selfFormal), _2494_params);
        } else {
          RAST._IType _2505_tpe;
          RAST._IType _out84;
          _out84 = (this).GenType(enclosingType, false, false);
          _2505_tpe = _out84;
          if (!((_2505_tpe).CanReadWithoutClone())) {
            _2505_tpe = RAST.Type.create_Borrowed(_2505_tpe);
          }
          _2494_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_2503_selfId, _2505_tpe)), _2494_params);
        }
        _2502_selfIdentifier = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2503_selfId);
      }
      Dafny.ISequence<RAST._IType> _2506_retTypeArgs;
      _2506_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _2507_typeI;
      _2507_typeI = BigInteger.Zero;
      while ((_2507_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _2508_typeExpr;
        RAST._IType _out85;
        _out85 = (this).GenType(((m).dtor_outTypes).Select(_2507_typeI), false, false);
        _2508_typeExpr = _out85;
        _2506_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2506_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2508_typeExpr));
        _2507_typeI = (_2507_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _2509_visibility;
      _2509_visibility = RAST.Visibility.create_PUB();
      Dafny.ISequence<DAST._ITypeArgDecl> _2510_typeParamsFiltered;
      _2510_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi24 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _2511_typeParamI = BigInteger.Zero; _2511_typeParamI < _hi24; _2511_typeParamI++) {
        DAST._ITypeArgDecl _2512_typeParam;
        _2512_typeParam = ((m).dtor_typeParams).Select(_2511_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_2512_typeParam).dtor_name)))) {
          _2510_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_2510_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_2512_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _2513_typeParams;
      _2513_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_2510_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi25 = new BigInteger((_2510_typeParamsFiltered).Count);
        for (BigInteger _2514_i = BigInteger.Zero; _2514_i < _hi25; _2514_i++) {
          DAST._IType _2515_typeArg;
          RAST._ITypeParamDecl _2516_rTypeParamDecl;
          DAST._IType _out86;
          RAST._ITypeParamDecl _out87;
          (this).GenTypeParam((_2510_typeParamsFiltered).Select(_2514_i), out _out86, out _out87);
          _2515_typeArg = _out86;
          _2516_rTypeParamDecl = _out87;
          _2513_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_2513_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_2516_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _2517_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _2518_env = DCOMP.Environment.Default();
      RAST._IExpr _2519_preBody;
      _2519_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if ((m).dtor_hasBody) {
        RAST._IExpr _2520_earlyReturn;
        _2520_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source83 = (m).dtor_outVars;
        if (_source83.is_None) {
        } else {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2521___mcc_h0 = _source83.dtor_value;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2522_outVars = _2521___mcc_h0;
          {
            Dafny.ISequence<RAST._IExpr> _2523_tupleArgs;
            _2523_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi26 = new BigInteger((_2522_outVars).Count);
            for (BigInteger _2524_outI = BigInteger.Zero; _2524_outI < _hi26; _2524_outI++) {
              Dafny.ISequence<Dafny.Rune> _2525_outVar;
              _2525_outVar = (_2522_outVars).Select(_2524_outI);
              RAST._IType _2526_outType;
              RAST._IType _out88;
              _out88 = (this).GenType(((m).dtor_outTypes).Select(_2524_outI), false, false);
              _2526_outType = _out88;
              Dafny.ISequence<Dafny.Rune> _2527_outName;
              _2527_outName = DCOMP.__default.escapeName((_2525_outVar));
              _2495_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2495_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2527_outName));
              RAST._IType _2528_outMaybeType;
              _2528_outMaybeType = (((_2526_outType).CanReadWithoutClone()) ? (_2526_outType) : (RAST.Type.create_Borrowed(_2526_outType)));
              _2496_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2496_paramTypes, _2527_outName, _2528_outMaybeType);
              RAST._IExpr _2529_outVarReturn;
              DCOMP._IOwnership _2530___v50;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2531___v51;
              RAST._IExpr _out89;
              DCOMP._IOwnership _out90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
              (this).GenExpr(DAST.Expression.create_Ident((_2525_outVar)), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2527_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_2527_outName, _2528_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out89, out _out90, out _out91);
              _2529_outVarReturn = _out89;
              _2530___v50 = _out90;
              _2531___v51 = _out91;
              _2523_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2523_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2529_outVarReturn));
            }
            if ((new BigInteger((_2523_tupleArgs).Count)) == (BigInteger.One)) {
              _2520_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_2523_tupleArgs).Select(BigInteger.Zero)));
            } else {
              _2520_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_2523_tupleArgs)));
            }
          }
        }
        _2518_env = DCOMP.Environment.create(_2495_paramNames, _2496_paramTypes);
        RAST._IExpr _2532_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2533___v52;
        DCOMP._IEnvironment _2534___v53;
        RAST._IExpr _out92;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out93;
        DCOMP._IEnvironment _out94;
        (this).GenStmts((m).dtor_body, _2502_selfIdentifier, _2518_env, true, _2520_earlyReturn, out _out92, out _out93, out _out94);
        _2532_body = _out92;
        _2533___v52 = _out93;
        _2534___v53 = _out94;
        _2517_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_2519_preBody).Then(_2532_body));
      } else {
        _2518_env = DCOMP.Environment.create(_2495_paramNames, _2496_paramTypes);
        _2517_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_2509_visibility, RAST.Fn.create(_2501_fnName, _2513_typeParams, _2494_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_2506_retTypeArgs).Count)) == (BigInteger.One)) ? ((_2506_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_2506_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _2517_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2535_declarations;
      _2535_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _2536_i;
      _2536_i = BigInteger.Zero;
      newEnv = env;
      while ((_2536_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _2537_stmt;
        _2537_stmt = (stmts).Select(_2536_i);
        RAST._IExpr _2538_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2539_recIdents;
        DCOMP._IEnvironment _2540_newEnv2;
        RAST._IExpr _out95;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
        DCOMP._IEnvironment _out97;
        (this).GenStmt(_2537_stmt, selfIdent, newEnv, (isLast) && ((_2536_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out95, out _out96, out _out97);
        _2538_stmtExpr = _out95;
        _2539_recIdents = _out96;
        _2540_newEnv2 = _out97;
        newEnv = _2540_newEnv2;
        DAST._IStatement _source84 = _2537_stmt;
        if (_source84.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _2541___mcc_h0 = _source84.dtor_name;
          DAST._IType _2542___mcc_h1 = _source84.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> _2543___mcc_h2 = _source84.dtor_maybeValue;
          Dafny.ISequence<Dafny.Rune> _2544_name = _2541___mcc_h0;
          {
            _2535_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2535_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_2544_name)));
          }
        } else if (_source84.is_Assign) {
          DAST._IAssignLhs _2545___mcc_h6 = _source84.dtor_lhs;
          DAST._IExpression _2546___mcc_h7 = _source84.dtor_value;
        } else if (_source84.is_If) {
          DAST._IExpression _2547___mcc_h10 = _source84.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2548___mcc_h11 = _source84.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _2549___mcc_h12 = _source84.dtor_els;
        } else if (_source84.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _2550___mcc_h16 = _source84.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _2551___mcc_h17 = _source84.dtor_body;
        } else if (_source84.is_While) {
          DAST._IExpression _2552___mcc_h20 = _source84.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _2553___mcc_h21 = _source84.dtor_body;
        } else if (_source84.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _2554___mcc_h24 = _source84.dtor_boundName;
          DAST._IType _2555___mcc_h25 = _source84.dtor_boundType;
          DAST._IExpression _2556___mcc_h26 = _source84.dtor_over;
          Dafny.ISequence<DAST._IStatement> _2557___mcc_h27 = _source84.dtor_body;
        } else if (_source84.is_Call) {
          DAST._IExpression _2558___mcc_h32 = _source84.dtor_on;
          DAST._ICallName _2559___mcc_h33 = _source84.dtor_callName;
          Dafny.ISequence<DAST._IType> _2560___mcc_h34 = _source84.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2561___mcc_h35 = _source84.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2562___mcc_h36 = _source84.dtor_outs;
        } else if (_source84.is_Return) {
          DAST._IExpression _2563___mcc_h42 = _source84.dtor_expr;
        } else if (_source84.is_EarlyReturn) {
        } else if (_source84.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2564___mcc_h44 = _source84.dtor_toLabel;
        } else if (_source84.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _2565___mcc_h46 = _source84.dtor_body;
        } else if (_source84.is_JumpTailCallStart) {
        } else if (_source84.is_Halt) {
        } else {
          DAST._IExpression _2566___mcc_h48 = _source84.dtor_Print_i_a0;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2539_recIdents, _2535_declarations));
        generated = (generated).Then(_2538_stmtExpr);
        _2536_i = (_2536_i) + (BigInteger.One);
      }
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source85 = lhs;
      if (_source85.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _2567___mcc_h0 = _source85.dtor_ident;
        Dafny.ISequence<Dafny.Rune> _source86 = _2567___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _2568___mcc_h1 = _source86;
        Dafny.ISequence<Dafny.Rune> _2569_id = _2568___mcc_h1;
        {
          Dafny.ISequence<Dafny.Rune> _2570_idRust;
          _2570_idRust = DCOMP.__default.escapeName(_2569_id);
          if (((env).IsBorrowed(_2570_idRust)) || ((env).IsBorrowedMut(_2570_idRust))) {
            generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _2570_idRust), rhs);
          } else {
            generated = RAST.__default.AssignVar(_2570_idRust, rhs);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2570_idRust);
          needsIIFE = false;
        }
      } else if (_source85.is_Select) {
        DAST._IExpression _2571___mcc_h2 = _source85.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2572___mcc_h3 = _source85.dtor_field;
        Dafny.ISequence<Dafny.Rune> _2573_field = _2572___mcc_h3;
        DAST._IExpression _2574_on = _2571___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _2575_fieldName;
          _2575_fieldName = DCOMP.__default.escapeName(_2573_field);
          RAST._IExpr _2576_onExpr;
          DCOMP._IOwnership _2577_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2578_recIdents;
          RAST._IExpr _out98;
          DCOMP._IOwnership _out99;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
          (this).GenExpr(_2574_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out98, out _out99, out _out100);
          _2576_onExpr = _out98;
          _2577_onOwned = _out99;
          _2578_recIdents = _out100;
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), (_2576_onExpr)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _2575_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), (rhs)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")));
          readIdents = _2578_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _2579___mcc_h4 = _source85.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2580___mcc_h5 = _source85.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2581_indices = _2580___mcc_h5;
        DAST._IExpression _2582_on = _2579___mcc_h4;
        {
          RAST._IExpr _2583_onExpr;
          DCOMP._IOwnership _2584_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2585_recIdents;
          RAST._IExpr _out101;
          DCOMP._IOwnership _out102;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out103;
          (this).GenExpr(_2582_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out101, out _out102, out _out103);
          _2583_onExpr = _out101;
          _2584_onOwned = _out102;
          _2585_recIdents = _out103;
          readIdents = _2585_recIdents;
          Dafny.ISequence<Dafny.Rune> _2586_r;
          _2586_r = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _2587_i;
          _2587_i = BigInteger.Zero;
          while ((_2587_i) < (new BigInteger((_2581_indices).Count))) {
            RAST._IExpr _2588_idx;
            DCOMP._IOwnership _2589___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2590_recIdentsIdx;
            RAST._IExpr _out104;
            DCOMP._IOwnership _out105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out106;
            (this).GenExpr((_2581_indices).Select(_2587_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out104, out _out105, out _out106);
            _2588_idx = _out104;
            _2589___v57 = _out105;
            _2590_recIdentsIdx = _out106;
            _2586_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2586_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), Std.Strings.__default.OfNat(_2587_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), (_2588_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2590_recIdentsIdx);
            _2587_i = (_2587_i) + (BigInteger.One);
          }
          _2586_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2586_r, (_2583_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _2587_i = BigInteger.Zero;
          while ((_2587_i) < (new BigInteger((_2581_indices).Count))) {
            _2586_r = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2586_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), Std.Strings.__default.OfNat(_2587_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _2587_i = (_2587_i) + (BigInteger.One);
          }
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2586_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), (rhs)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}")));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source87 = stmt;
      if (_source87.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _2591___mcc_h0 = _source87.dtor_name;
        DAST._IType _2592___mcc_h1 = _source87.dtor_typ;
        Std.Wrappers._IOption<DAST._IExpression> _2593___mcc_h2 = _source87.dtor_maybeValue;
        Std.Wrappers._IOption<DAST._IExpression> _source88 = _2593___mcc_h2;
        if (_source88.is_None) {
          DAST._IType _2594_typ = _2592___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2595_name = _2591___mcc_h0;
          {
            DAST._IStatement _2596_newStmt;
            _2596_newStmt = DAST.Statement.create_DeclareVar(_2595_name, _2594_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_2594_typ)));
            RAST._IExpr _out107;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
            DCOMP._IEnvironment _out109;
            (this).GenStmt(_2596_newStmt, selfIdent, env, isLast, earlyReturn, out _out107, out _out108, out _out109);
            generated = _out107;
            readIdents = _out108;
            newEnv = _out109;
          }
        } else {
          DAST._IExpression _2597___mcc_h3 = _source88.dtor_value;
          DAST._IExpression _2598_expression = _2597___mcc_h3;
          DAST._IType _2599_typ = _2592___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _2600_name = _2591___mcc_h0;
          {
            RAST._IType _2601_tpe;
            RAST._IType _out110;
            _out110 = (this).GenType(_2599_typ, true, false);
            _2601_tpe = _out110;
            RAST._IExpr _2602_expr;
            DCOMP._IOwnership _2603_exprOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2604_recIdents;
            RAST._IExpr _out111;
            DCOMP._IOwnership _out112;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
            (this).GenExpr(_2598_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out111, out _out112, out _out113);
            _2602_expr = _out111;
            _2603_exprOwnership = _out112;
            _2604_recIdents = _out113;
            readIdents = _2604_recIdents;
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_2600_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2601_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2602_expr));
            newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_2600_name), _2601_tpe);
          }
        }
      } else if (_source87.is_Assign) {
        DAST._IAssignLhs _2605___mcc_h4 = _source87.dtor_lhs;
        DAST._IExpression _2606___mcc_h5 = _source87.dtor_value;
        DAST._IExpression _2607_expression = _2606___mcc_h5;
        DAST._IAssignLhs _2608_lhs = _2605___mcc_h4;
        {
          RAST._IExpr _2609_exprGen;
          DCOMP._IOwnership _2610___v58;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2611_exprIdents;
          RAST._IExpr _out114;
          DCOMP._IOwnership _out115;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
          (this).GenExpr(_2607_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out114, out _out115, out _out116);
          _2609_exprGen = _out114;
          _2610___v58 = _out115;
          _2611_exprIdents = _out116;
          if ((_2608_lhs).is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2612_rustId;
            _2612_rustId = DCOMP.__default.escapeName(((_2608_lhs).dtor_ident));
            Std.Wrappers._IOption<RAST._IType> _2613_tpe;
            _2613_tpe = (env).GetType(_2612_rustId);
          }
          RAST._IExpr _2614_lhsGen;
          bool _2615_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2616_recIdents;
          DCOMP._IEnvironment _2617_resEnv;
          RAST._IExpr _out117;
          bool _out118;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
          DCOMP._IEnvironment _out120;
          (this).GenAssignLhs(_2608_lhs, _2609_exprGen, selfIdent, env, out _out117, out _out118, out _out119, out _out120);
          _2614_lhsGen = _out117;
          _2615_needsIIFE = _out118;
          _2616_recIdents = _out119;
          _2617_resEnv = _out120;
          generated = _2614_lhsGen;
          newEnv = _2617_resEnv;
          if (_2615_needsIIFE) {
            generated = RAST.Expr.create_Block(generated);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2616_recIdents, _2611_exprIdents);
        }
      } else if (_source87.is_If) {
        DAST._IExpression _2618___mcc_h6 = _source87.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2619___mcc_h7 = _source87.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _2620___mcc_h8 = _source87.dtor_els;
        Dafny.ISequence<DAST._IStatement> _2621_elsDafny = _2620___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _2622_thnDafny = _2619___mcc_h7;
        DAST._IExpression _2623_cond = _2618___mcc_h6;
        {
          RAST._IExpr _2624_cond;
          DCOMP._IOwnership _2625___v59;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2626_recIdents;
          RAST._IExpr _out121;
          DCOMP._IOwnership _out122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
          (this).GenExpr(_2623_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out121, out _out122, out _out123);
          _2624_cond = _out121;
          _2625___v59 = _out122;
          _2626_recIdents = _out123;
          Dafny.ISequence<Dafny.Rune> _2627_condString;
          _2627_condString = (_2624_cond)._ToString(DCOMP.__default.IND);
          readIdents = _2626_recIdents;
          RAST._IExpr _2628_thn;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2629_thnIdents;
          DCOMP._IEnvironment _2630_thnEnv;
          RAST._IExpr _out124;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out125;
          DCOMP._IEnvironment _out126;
          (this).GenStmts(_2622_thnDafny, selfIdent, env, isLast, earlyReturn, out _out124, out _out125, out _out126);
          _2628_thn = _out124;
          _2629_thnIdents = _out125;
          _2630_thnEnv = _out126;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2629_thnIdents);
          RAST._IExpr _2631_els;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2632_elsIdents;
          DCOMP._IEnvironment _2633_elsEnv;
          RAST._IExpr _out127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
          DCOMP._IEnvironment _out129;
          (this).GenStmts(_2621_elsDafny, selfIdent, env, isLast, earlyReturn, out _out127, out _out128, out _out129);
          _2631_els = _out127;
          _2632_elsIdents = _out128;
          _2633_elsEnv = _out129;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2632_elsIdents);
          newEnv = env;
          generated = RAST.Expr.create_IfExpr(_2624_cond, _2628_thn, _2631_els);
        }
      } else if (_source87.is_Labeled) {
        Dafny.ISequence<Dafny.Rune> _2634___mcc_h9 = _source87.dtor_lbl;
        Dafny.ISequence<DAST._IStatement> _2635___mcc_h10 = _source87.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2636_body = _2635___mcc_h10;
        Dafny.ISequence<Dafny.Rune> _2637_lbl = _2634___mcc_h9;
        {
          RAST._IExpr _2638_body;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2639_bodyIdents;
          DCOMP._IEnvironment _2640_env2;
          RAST._IExpr _out130;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
          DCOMP._IEnvironment _out132;
          (this).GenStmts(_2636_body, selfIdent, env, isLast, earlyReturn, out _out130, out _out131, out _out132);
          _2638_body = _out130;
          _2639_bodyIdents = _out131;
          _2640_env2 = _out132;
          readIdents = _2639_bodyIdents;
          generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2637_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_2638_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
          newEnv = env;
        }
      } else if (_source87.is_While) {
        DAST._IExpression _2641___mcc_h11 = _source87.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _2642___mcc_h12 = _source87.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2643_body = _2642___mcc_h12;
        DAST._IExpression _2644_cond = _2641___mcc_h11;
        {
          RAST._IExpr _2645_cond;
          DCOMP._IOwnership _2646___v60;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2647_recIdents;
          RAST._IExpr _out133;
          DCOMP._IOwnership _out134;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
          (this).GenExpr(_2644_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
          _2645_cond = _out133;
          _2646___v60 = _out134;
          _2647_recIdents = _out135;
          readIdents = _2647_recIdents;
          RAST._IExpr _2648_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2649_bodyIdents;
          DCOMP._IEnvironment _2650_bodyEnv;
          RAST._IExpr _out136;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
          DCOMP._IEnvironment _out138;
          (this).GenStmts(_2643_body, selfIdent, env, false, earlyReturn, out _out136, out _out137, out _out138);
          _2648_bodyExpr = _out136;
          _2649_bodyIdents = _out137;
          _2650_bodyEnv = _out138;
          newEnv = env;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2649_bodyIdents);
          generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2645_cond), _2648_bodyExpr);
        }
      } else if (_source87.is_Foreach) {
        Dafny.ISequence<Dafny.Rune> _2651___mcc_h13 = _source87.dtor_boundName;
        DAST._IType _2652___mcc_h14 = _source87.dtor_boundType;
        DAST._IExpression _2653___mcc_h15 = _source87.dtor_over;
        Dafny.ISequence<DAST._IStatement> _2654___mcc_h16 = _source87.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2655_body = _2654___mcc_h16;
        DAST._IExpression _2656_over = _2653___mcc_h15;
        DAST._IType _2657_boundType = _2652___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _2658_boundName = _2651___mcc_h13;
        {
          RAST._IExpr _2659_over;
          DCOMP._IOwnership _2660___v61;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2661_recIdents;
          RAST._IExpr _out139;
          DCOMP._IOwnership _out140;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
          (this).GenExpr(_2656_over, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
          _2659_over = _out139;
          _2660___v61 = _out140;
          _2661_recIdents = _out141;
          RAST._IType _2662_boundTpe;
          RAST._IType _out142;
          _out142 = (this).GenType(_2657_boundType, false, false);
          _2662_boundTpe = _out142;
          readIdents = _2661_recIdents;
          Dafny.ISequence<Dafny.Rune> _2663_boundRName;
          _2663_boundRName = DCOMP.__default.escapeName(_2658_boundName);
          RAST._IExpr _2664_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2665_bodyIdents;
          DCOMP._IEnvironment _2666_bodyEnv;
          RAST._IExpr _out143;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
          DCOMP._IEnvironment _out145;
          (this).GenStmts(_2655_body, selfIdent, (env).AddAssigned(_2663_boundRName, _2662_boundTpe), false, earlyReturn, out _out143, out _out144, out _out145);
          _2664_bodyExpr = _out143;
          _2665_bodyIdents = _out144;
          _2666_bodyEnv = _out145;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2665_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2663_boundRName));
          newEnv = env;
          generated = RAST.Expr.create_For(_2663_boundRName, _2659_over, _2664_bodyExpr);
        }
      } else if (_source87.is_Call) {
        DAST._IExpression _2667___mcc_h17 = _source87.dtor_on;
        DAST._ICallName _2668___mcc_h18 = _source87.dtor_callName;
        Dafny.ISequence<DAST._IType> _2669___mcc_h19 = _source87.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2670___mcc_h20 = _source87.dtor_args;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2671___mcc_h21 = _source87.dtor_outs;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _2672_maybeOutVars = _2671___mcc_h21;
        Dafny.ISequence<DAST._IExpression> _2673_args = _2670___mcc_h20;
        Dafny.ISequence<DAST._IType> _2674_typeArgs = _2669___mcc_h19;
        DAST._ICallName _2675_name = _2668___mcc_h18;
        DAST._IExpression _2676_on = _2667___mcc_h17;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _2677_onExpr;
          DCOMP._IOwnership _2678___v64;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2679_enclosingIdents;
          RAST._IExpr _out146;
          DCOMP._IOwnership _out147;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
          (this).GenExpr(_2676_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out146, out _out147, out _out148);
          _2677_onExpr = _out146;
          _2678___v64 = _out147;
          _2679_enclosingIdents = _out148;
          Dafny.ISequence<RAST._IType> _2680_typeArgsR;
          _2680_typeArgsR = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_2674_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2681_typeI;
            _2681_typeI = BigInteger.Zero;
            while ((_2681_typeI) < (new BigInteger((_2674_typeArgs).Count))) {
              RAST._IType _2682_tpe;
              RAST._IType _out149;
              _out149 = (this).GenType((_2674_typeArgs).Select(_2681_typeI), false, false);
              _2682_tpe = _out149;
              _2680_typeArgsR = Dafny.Sequence<RAST._IType>.Concat(_2680_typeArgsR, Dafny.Sequence<RAST._IType>.FromElements(_2682_tpe));
              _2681_typeI = (_2681_typeI) + (BigInteger.One);
            }
          }
          Dafny.ISequence<RAST._IExpr> _2683_argExprs;
          _2683_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi27 = new BigInteger((_2673_args).Count);
          for (BigInteger _2684_i = BigInteger.Zero; _2684_i < _hi27; _2684_i++) {
            DCOMP._IOwnership _2685_argOwnership;
            _2685_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_2675_name).is_CallName) && ((_2684_i) < (new BigInteger((((_2675_name).dtor_signature)).Count)))) {
              RAST._IType _2686_tpe;
              RAST._IType _out150;
              _out150 = (this).GenType(((((_2675_name).dtor_signature)).Select(_2684_i)).dtor_typ, false, false);
              _2686_tpe = _out150;
              if ((_2686_tpe).CanReadWithoutClone()) {
                _2685_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _2687_argExpr;
            DCOMP._IOwnership _2688_ownership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2689_argIdents;
            RAST._IExpr _out151;
            DCOMP._IOwnership _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            (this).GenExpr((_2673_args).Select(_2684_i), selfIdent, env, _2685_argOwnership, out _out151, out _out152, out _out153);
            _2687_argExpr = _out151;
            _2688_ownership = _out152;
            _2689_argIdents = _out153;
            _2683_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2683_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2687_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2689_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2679_enclosingIdents);
          Dafny.ISequence<Dafny.Rune> _2690_renderedName;
          _2690_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source89) => {
            if (_source89.is_CallName) {
              Dafny.ISequence<Dafny.Rune> _2691___mcc_h26 = _source89.dtor_name;
              Std.Wrappers._IOption<DAST._IType> _2692___mcc_h27 = _source89.dtor_onType;
              Dafny.ISequence<DAST._IFormal> _2693___mcc_h28 = _source89.dtor_signature;
              Dafny.ISequence<Dafny.Rune> _2694_name = _2691___mcc_h26;
              return DCOMP.__default.escapeName(_2694_name);
            } else if (_source89.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source89.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source89.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_2675_name);
          DAST._IExpression _source90 = _2676_on;
          if (_source90.is_Literal) {
            DAST._ILiteral _2695___mcc_h29 = _source90.dtor_Literal_i_a0;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2696___mcc_h31 = _source90.dtor_Ident_i_a0;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2697___mcc_h33 = _source90.dtor_Companion_i_a0;
            {
              _2677_onExpr = (_2677_onExpr).MSel(_2690_renderedName);
            }
          } else if (_source90.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2698___mcc_h35 = _source90.dtor_Tuple_i_a0;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2699___mcc_h37 = _source90.dtor_path;
            Dafny.ISequence<DAST._IType> _2700___mcc_h38 = _source90.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2701___mcc_h39 = _source90.dtor_args;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2702___mcc_h43 = _source90.dtor_dims;
            DAST._IType _2703___mcc_h44 = _source90.dtor_typ;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_DatatypeValue) {
            DAST._IDatatypeType _2704___mcc_h47 = _source90.dtor_datatypeType;
            Dafny.ISequence<DAST._IType> _2705___mcc_h48 = _source90.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2706___mcc_h49 = _source90.dtor_variant;
            bool _2707___mcc_h50 = _source90.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2708___mcc_h51 = _source90.dtor_contents;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_Convert) {
            DAST._IExpression _2709___mcc_h57 = _source90.dtor_value;
            DAST._IType _2710___mcc_h58 = _source90.dtor_from;
            DAST._IType _2711___mcc_h59 = _source90.dtor_typ;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_SeqConstruct) {
            DAST._IExpression _2712___mcc_h63 = _source90.dtor_length;
            DAST._IExpression _2713___mcc_h64 = _source90.dtor_elem;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2714___mcc_h67 = _source90.dtor_elements;
            DAST._IType _2715___mcc_h68 = _source90.dtor_typ;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2716___mcc_h71 = _source90.dtor_elements;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _2717___mcc_h73 = _source90.dtor_elements;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2718___mcc_h75 = _source90.dtor_mapElems;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_MapBuilder) {
            DAST._IType _2719___mcc_h77 = _source90.dtor_keyType;
            DAST._IType _2720___mcc_h78 = _source90.dtor_valueType;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_SeqUpdate) {
            DAST._IExpression _2721___mcc_h81 = _source90.dtor_expr;
            DAST._IExpression _2722___mcc_h82 = _source90.dtor_indexExpr;
            DAST._IExpression _2723___mcc_h83 = _source90.dtor_value;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_MapUpdate) {
            DAST._IExpression _2724___mcc_h87 = _source90.dtor_expr;
            DAST._IExpression _2725___mcc_h88 = _source90.dtor_indexExpr;
            DAST._IExpression _2726___mcc_h89 = _source90.dtor_value;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_SetBuilder) {
            DAST._IType _2727___mcc_h93 = _source90.dtor_elemType;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_ToMultiset) {
            DAST._IExpression _2728___mcc_h95 = _source90.dtor_ToMultiset_i_a0;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_This) {
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_Ite) {
            DAST._IExpression _2729___mcc_h97 = _source90.dtor_cond;
            DAST._IExpression _2730___mcc_h98 = _source90.dtor_thn;
            DAST._IExpression _2731___mcc_h99 = _source90.dtor_els;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_UnOp) {
            DAST._IUnaryOp _2732___mcc_h103 = _source90.dtor_unOp;
            DAST._IExpression _2733___mcc_h104 = _source90.dtor_expr;
            DAST.Format._IUnaryOpFormat _2734___mcc_h105 = _source90.dtor_format1;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_BinOp) {
            DAST._IBinOp _2735___mcc_h109 = _source90.dtor_op;
            DAST._IExpression _2736___mcc_h110 = _source90.dtor_left;
            DAST._IExpression _2737___mcc_h111 = _source90.dtor_right;
            DAST.Format._IBinaryOpFormat _2738___mcc_h112 = _source90.dtor_format2;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_ArrayLen) {
            DAST._IExpression _2739___mcc_h117 = _source90.dtor_expr;
            BigInteger _2740___mcc_h118 = _source90.dtor_dim;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_MapKeys) {
            DAST._IExpression _2741___mcc_h121 = _source90.dtor_expr;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_MapValues) {
            DAST._IExpression _2742___mcc_h123 = _source90.dtor_expr;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_Select) {
            DAST._IExpression _2743___mcc_h125 = _source90.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2744___mcc_h126 = _source90.dtor_field;
            bool _2745___mcc_h127 = _source90.dtor_isConstant;
            bool _2746___mcc_h128 = _source90.dtor_onDatatype;
            DAST._IType _2747___mcc_h129 = _source90.dtor_fieldType;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_SelectFn) {
            DAST._IExpression _2748___mcc_h135 = _source90.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2749___mcc_h136 = _source90.dtor_field;
            bool _2750___mcc_h137 = _source90.dtor_onDatatype;
            bool _2751___mcc_h138 = _source90.dtor_isStatic;
            BigInteger _2752___mcc_h139 = _source90.dtor_arity;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_Index) {
            DAST._IExpression _2753___mcc_h145 = _source90.dtor_expr;
            DAST._ICollKind _2754___mcc_h146 = _source90.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _2755___mcc_h147 = _source90.dtor_indices;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_IndexRange) {
            DAST._IExpression _2756___mcc_h151 = _source90.dtor_expr;
            bool _2757___mcc_h152 = _source90.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _2758___mcc_h153 = _source90.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _2759___mcc_h154 = _source90.dtor_high;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_TupleSelect) {
            DAST._IExpression _2760___mcc_h159 = _source90.dtor_expr;
            BigInteger _2761___mcc_h160 = _source90.dtor_index;
            DAST._IType _2762___mcc_h161 = _source90.dtor_fieldType;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_Call) {
            DAST._IExpression _2763___mcc_h165 = _source90.dtor_on;
            DAST._ICallName _2764___mcc_h166 = _source90.dtor_callName;
            Dafny.ISequence<DAST._IType> _2765___mcc_h167 = _source90.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2766___mcc_h168 = _source90.dtor_args;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2767___mcc_h173 = _source90.dtor_params;
            DAST._IType _2768___mcc_h174 = _source90.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2769___mcc_h175 = _source90.dtor_body;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2770___mcc_h179 = _source90.dtor_values;
            DAST._IType _2771___mcc_h180 = _source90.dtor_retType;
            DAST._IExpression _2772___mcc_h181 = _source90.dtor_expr;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2773___mcc_h185 = _source90.dtor_name;
            DAST._IType _2774___mcc_h186 = _source90.dtor_typ;
            DAST._IExpression _2775___mcc_h187 = _source90.dtor_value;
            DAST._IExpression _2776___mcc_h188 = _source90.dtor_iifeBody;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_Apply) {
            DAST._IExpression _2777___mcc_h193 = _source90.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2778___mcc_h194 = _source90.dtor_args;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_TypeTest) {
            DAST._IExpression _2779___mcc_h197 = _source90.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2780___mcc_h198 = _source90.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2781___mcc_h199 = _source90.dtor_variant;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_InitializationValue) {
            DAST._IType _2782___mcc_h203 = _source90.dtor_typ;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_BoolBoundedPool) {
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_SetBoundedPool) {
            DAST._IExpression _2783___mcc_h205 = _source90.dtor_of;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else if (_source90.is_SeqBoundedPool) {
            DAST._IExpression _2784___mcc_h207 = _source90.dtor_of;
            bool _2785___mcc_h208 = _source90.dtor_includeDuplicates;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          } else {
            DAST._IExpression _2786___mcc_h211 = _source90.dtor_lo;
            DAST._IExpression _2787___mcc_h212 = _source90.dtor_hi;
            {
              _2677_onExpr = (_2677_onExpr).Sel(_2690_renderedName);
            }
          }
          generated = _2677_onExpr;
          if ((new BigInteger((_2680_typeArgsR).Count)).Sign == 1) {
            generated = (generated).ApplyType(_2680_typeArgsR);
          }
          generated = (generated).Apply(_2683_argExprs);
          if (((_2672_maybeOutVars).is_Some) && ((new BigInteger(((_2672_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
            Dafny.ISequence<Dafny.Rune> _2788_outVar;
            _2788_outVar = DCOMP.__default.escapeName((((_2672_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
            generated = RAST.__default.AssignVar(_2788_outVar, generated);
          } else if (((_2672_maybeOutVars).is_None) || ((new BigInteger(((_2672_maybeOutVars).dtor_value).Count)).Sign == 0)) {
          } else {
            Dafny.ISequence<Dafny.Rune> _2789_tmpVar;
            _2789_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
            RAST._IExpr _2790_tmpId;
            _2790_tmpId = RAST.Expr.create_Identifier(_2789_tmpVar);
            generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _2789_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2791_outVars;
            _2791_outVars = (_2672_maybeOutVars).dtor_value;
            BigInteger _hi28 = new BigInteger((_2791_outVars).Count);
            for (BigInteger _2792_outI = BigInteger.Zero; _2792_outI < _hi28; _2792_outI++) {
              Dafny.ISequence<Dafny.Rune> _2793_outVar;
              _2793_outVar = DCOMP.__default.escapeName(((_2791_outVars).Select(_2792_outI)));
              RAST._IExpr _2794_rhs;
              _2794_rhs = (_2790_tmpId).Sel(Std.Strings.__default.OfNat(_2792_outI));
              generated = (generated).Then(RAST.__default.AssignVar(_2793_outVar, _2794_rhs));
            }
          }
          newEnv = env;
        }
      } else if (_source87.is_Return) {
        DAST._IExpression _2795___mcc_h22 = _source87.dtor_expr;
        DAST._IExpression _2796_exprDafny = _2795___mcc_h22;
        {
          RAST._IExpr _2797_expr;
          DCOMP._IOwnership _2798___v69;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2799_recIdents;
          RAST._IExpr _out154;
          DCOMP._IOwnership _out155;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
          (this).GenExpr(_2796_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out154, out _out155, out _out156);
          _2797_expr = _out154;
          _2798___v69 = _out155;
          _2799_recIdents = _out156;
          readIdents = _2799_recIdents;
          if (isLast) {
            generated = _2797_expr;
          } else {
            generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_2797_expr));
          }
          newEnv = env;
        }
      } else if (_source87.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source87.is_Break) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2800___mcc_h23 = _source87.dtor_toLabel;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2801_toLabel = _2800___mcc_h23;
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source91 = _2801_toLabel;
          if (_source91.is_None) {
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2802___mcc_h215 = _source91.dtor_value;
            Dafny.ISequence<Dafny.Rune> _2803_lbl = _2802___mcc_h215;
            {
              generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _2803_lbl)));
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source87.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _2804___mcc_h24 = _source87.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2805_body = _2804___mcc_h24;
        {
          generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
          }
          newEnv = env;
          BigInteger _hi29 = new BigInteger(((env).dtor_names).Count);
          for (BigInteger _2806_paramI = BigInteger.Zero; _2806_paramI < _hi29; _2806_paramI++) {
            Dafny.ISequence<Dafny.Rune> _2807_param;
            _2807_param = ((env).dtor_names).Select(_2806_paramI);
            RAST._IExpr _2808_paramInit;
            DCOMP._IOwnership _2809___v62;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2810___v63;
            RAST._IExpr _out157;
            DCOMP._IOwnership _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            (this).GenIdent(_2807_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out157, out _out158, out _out159);
            _2808_paramInit = _out157;
            _2809___v62 = _out158;
            _2810___v63 = _out159;
            generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2807_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2808_paramInit)));
            if (((env).dtor_types).Contains(_2807_param)) {
              RAST._IType _2811_declaredType;
              _2811_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_2807_param)).ToOwned();
              newEnv = (newEnv).AddAssigned(_2807_param, _2811_declaredType);
            }
          }
          RAST._IExpr _2812_bodyExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2813_bodyIdents;
          DCOMP._IEnvironment _2814_bodyEnv;
          RAST._IExpr _out160;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
          DCOMP._IEnvironment _out162;
          (this).GenStmts(_2805_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), newEnv, false, earlyReturn, out _out160, out _out161, out _out162);
          _2812_bodyExpr = _out160;
          _2813_bodyIdents = _out161;
          _2814_bodyEnv = _out162;
          readIdents = _2813_bodyIdents;
          generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _2812_bodyExpr)));
        }
      } else if (_source87.is_JumpTailCallStart) {
        {
          generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else if (_source87.is_Halt) {
        {
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          newEnv = env;
        }
      } else {
        DAST._IExpression _2815___mcc_h25 = _source87.dtor_Print_i_a0;
        DAST._IExpression _2816_e = _2815___mcc_h25;
        {
          RAST._IExpr _2817_printedExpr;
          DCOMP._IOwnership _2818_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2819_recIdents;
          RAST._IExpr _out163;
          DCOMP._IOwnership _out164;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
          (this).GenExpr(_2816_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out163, out _out164, out _out165);
          _2817_printedExpr = _out163;
          _2818_recOwnership = _out164;
          _2819_recIdents = _out165;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_2817_printedExpr)));
          readIdents = _2819_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source92 = range;
      if (_source92.is_U8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
      } else if (_source92.is_I8) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
      } else if (_source92.is_U16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
      } else if (_source92.is_I16) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
      } else if (_source92.is_U32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
      } else if (_source92.is_I32) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
      } else if (_source92.is_U64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
      } else if (_source92.is_I64) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
      } else if (_source92.is_U128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
      } else if (_source92.is_I128) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
      } else if (_source92.is_BigInt) {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      } else {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public static void FromOwned(RAST._IExpr r, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
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
        @out = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      }
    }
    public static void FromOwnership(RAST._IExpr r, DCOMP._IOwnership ownership, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      if (object.Equals(ownership, expectedOwnership)) {
        @out = r;
        resultingOwnership = expectedOwnership;
        return ;
      }
      if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwned())) {
        RAST._IExpr _out166;
        DCOMP._IOwnership _out167;
        DCOMP.COMP.FromOwned(r, expectedOwnership, out _out166, out _out167);
        @out = _out166;
        resultingOwnership = _out167;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out168;
        DCOMP._IOwnership _out169;
        DCOMP.COMP.FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out168, out _out169);
        @out = _out168;
        resultingOwnership = _out169;
      } else if ((object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowedMut()))) {
        if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          @out = RAST.__default.Clone(r);
        } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
          @out = RAST.__default.BoxNew(RAST.__default.Clone(r));
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
    public void GenExprLiteral(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source93 = e;
      DAST._ILiteral _2820___mcc_h0 = _source93.dtor_Literal_i_a0;
      DAST._ILiteral _source94 = _2820___mcc_h0;
      if (_source94.is_BoolLiteral) {
        bool _2821___mcc_h1 = _source94.dtor_BoolLiteral_i_a0;
        bool _2822_b = _2821___mcc_h1;
        {
          RAST._IExpr _out170;
          DCOMP._IOwnership _out171;
          DCOMP.COMP.FromOwned(RAST.Expr.create_LiteralBool(_2822_b), expectedOwnership, out _out170, out _out171);
          r = _out170;
          resultingOwnership = _out171;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source94.is_IntLiteral) {
        Dafny.ISequence<Dafny.Rune> _2823___mcc_h2 = _source94.dtor_IntLiteral_i_a0;
        DAST._IType _2824___mcc_h3 = _source94.dtor_IntLiteral_i_a1;
        DAST._IType _2825_t = _2824___mcc_h3;
        Dafny.ISequence<Dafny.Rune> _2826_i = _2823___mcc_h2;
        {
          DAST._IType _source95 = _2825_t;
          if (_source95.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2827___mcc_h102 = _source95.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2828___mcc_h103 = _source95.dtor_typeArgs;
            DAST._IResolvedType _2829___mcc_h104 = _source95.dtor_resolved;
            DAST._IType _2830_o = _2825_t;
            {
              RAST._IType _2831_genType;
              RAST._IType _out172;
              _out172 = (this).GenType(_2830_o, false, false);
              _2831_genType = _out172;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2831_genType);
            }
          } else if (_source95.is_Nullable) {
            DAST._IType _2832___mcc_h108 = _source95.dtor_Nullable_i_a0;
            DAST._IType _2833_o = _2825_t;
            {
              RAST._IType _2834_genType;
              RAST._IType _out173;
              _out173 = (this).GenType(_2833_o, false, false);
              _2834_genType = _out173;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2834_genType);
            }
          } else if (_source95.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2835___mcc_h110 = _source95.dtor_Tuple_i_a0;
            DAST._IType _2836_o = _2825_t;
            {
              RAST._IType _2837_genType;
              RAST._IType _out174;
              _out174 = (this).GenType(_2836_o, false, false);
              _2837_genType = _out174;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2837_genType);
            }
          } else if (_source95.is_Array) {
            DAST._IType _2838___mcc_h112 = _source95.dtor_element;
            BigInteger _2839___mcc_h113 = _source95.dtor_dims;
            DAST._IType _2840_o = _2825_t;
            {
              RAST._IType _2841_genType;
              RAST._IType _out175;
              _out175 = (this).GenType(_2840_o, false, false);
              _2841_genType = _out175;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2841_genType);
            }
          } else if (_source95.is_Seq) {
            DAST._IType _2842___mcc_h116 = _source95.dtor_element;
            DAST._IType _2843_o = _2825_t;
            {
              RAST._IType _2844_genType;
              RAST._IType _out176;
              _out176 = (this).GenType(_2843_o, false, false);
              _2844_genType = _out176;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2844_genType);
            }
          } else if (_source95.is_Set) {
            DAST._IType _2845___mcc_h118 = _source95.dtor_element;
            DAST._IType _2846_o = _2825_t;
            {
              RAST._IType _2847_genType;
              RAST._IType _out177;
              _out177 = (this).GenType(_2846_o, false, false);
              _2847_genType = _out177;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2847_genType);
            }
          } else if (_source95.is_Multiset) {
            DAST._IType _2848___mcc_h120 = _source95.dtor_element;
            DAST._IType _2849_o = _2825_t;
            {
              RAST._IType _2850_genType;
              RAST._IType _out178;
              _out178 = (this).GenType(_2849_o, false, false);
              _2850_genType = _out178;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2850_genType);
            }
          } else if (_source95.is_Map) {
            DAST._IType _2851___mcc_h122 = _source95.dtor_key;
            DAST._IType _2852___mcc_h123 = _source95.dtor_value;
            DAST._IType _2853_o = _2825_t;
            {
              RAST._IType _2854_genType;
              RAST._IType _out179;
              _out179 = (this).GenType(_2853_o, false, false);
              _2854_genType = _out179;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2854_genType);
            }
          } else if (_source95.is_SetBuilder) {
            DAST._IType _2855___mcc_h126 = _source95.dtor_element;
            DAST._IType _2856_o = _2825_t;
            {
              RAST._IType _2857_genType;
              RAST._IType _out180;
              _out180 = (this).GenType(_2856_o, false, false);
              _2857_genType = _out180;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2857_genType);
            }
          } else if (_source95.is_MapBuilder) {
            DAST._IType _2858___mcc_h128 = _source95.dtor_key;
            DAST._IType _2859___mcc_h129 = _source95.dtor_value;
            DAST._IType _2860_o = _2825_t;
            {
              RAST._IType _2861_genType;
              RAST._IType _out181;
              _out181 = (this).GenType(_2860_o, false, false);
              _2861_genType = _out181;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2861_genType);
            }
          } else if (_source95.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2862___mcc_h132 = _source95.dtor_args;
            DAST._IType _2863___mcc_h133 = _source95.dtor_result;
            DAST._IType _2864_o = _2825_t;
            {
              RAST._IType _2865_genType;
              RAST._IType _out182;
              _out182 = (this).GenType(_2864_o, false, false);
              _2865_genType = _out182;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2865_genType);
            }
          } else if (_source95.is_Primitive) {
            DAST._IPrimitive _2866___mcc_h136 = _source95.dtor_Primitive_i_a0;
            DAST._IPrimitive _source96 = _2866___mcc_h136;
            if (_source96.is_Int) {
              {
                if ((new BigInteger((_2826_i).Count)) <= (new BigInteger(4))) {
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_2826_i));
                } else {
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_2826_i, true));
                }
              }
            } else if (_source96.is_Real) {
              DAST._IType _2867_o = _2825_t;
              {
                RAST._IType _2868_genType;
                RAST._IType _out183;
                _out183 = (this).GenType(_2867_o, false, false);
                _2868_genType = _out183;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2868_genType);
              }
            } else if (_source96.is_String) {
              DAST._IType _2869_o = _2825_t;
              {
                RAST._IType _2870_genType;
                RAST._IType _out184;
                _out184 = (this).GenType(_2869_o, false, false);
                _2870_genType = _out184;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2870_genType);
              }
            } else if (_source96.is_Bool) {
              DAST._IType _2871_o = _2825_t;
              {
                RAST._IType _2872_genType;
                RAST._IType _out185;
                _out185 = (this).GenType(_2871_o, false, false);
                _2872_genType = _out185;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2872_genType);
              }
            } else {
              DAST._IType _2873_o = _2825_t;
              {
                RAST._IType _2874_genType;
                RAST._IType _out186;
                _out186 = (this).GenType(_2873_o, false, false);
                _2874_genType = _out186;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2874_genType);
              }
            }
          } else if (_source95.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2875___mcc_h138 = _source95.dtor_Passthrough_i_a0;
            DAST._IType _2876_o = _2825_t;
            {
              RAST._IType _2877_genType;
              RAST._IType _out187;
              _out187 = (this).GenType(_2876_o, false, false);
              _2877_genType = _out187;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2877_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2878___mcc_h140 = _source95.dtor_TypeArg_i_a0;
            DAST._IType _2879_o = _2825_t;
            {
              RAST._IType _2880_genType;
              RAST._IType _out188;
              _out188 = (this).GenType(_2879_o, false, false);
              _2880_genType = _out188;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_2826_i), _2880_genType);
            }
          }
          RAST._IExpr _out189;
          DCOMP._IOwnership _out190;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out189, out _out190);
          r = _out189;
          resultingOwnership = _out190;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source94.is_DecLiteral) {
        Dafny.ISequence<Dafny.Rune> _2881___mcc_h4 = _source94.dtor_DecLiteral_i_a0;
        Dafny.ISequence<Dafny.Rune> _2882___mcc_h5 = _source94.dtor_DecLiteral_i_a1;
        DAST._IType _2883___mcc_h6 = _source94.dtor_DecLiteral_i_a2;
        DAST._IType _2884_t = _2883___mcc_h6;
        Dafny.ISequence<Dafny.Rune> _2885_d = _2882___mcc_h5;
        Dafny.ISequence<Dafny.Rune> _2886_n = _2881___mcc_h4;
        {
          DAST._IType _source97 = _2884_t;
          if (_source97.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2887___mcc_h142 = _source97.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _2888___mcc_h143 = _source97.dtor_typeArgs;
            DAST._IResolvedType _2889___mcc_h144 = _source97.dtor_resolved;
            DAST._IType _2890_o = _2884_t;
            {
              RAST._IType _2891_genType;
              RAST._IType _out191;
              _out191 = (this).GenType(_2890_o, false, false);
              _2891_genType = _out191;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2891_genType);
            }
          } else if (_source97.is_Nullable) {
            DAST._IType _2892___mcc_h148 = _source97.dtor_Nullable_i_a0;
            DAST._IType _2893_o = _2884_t;
            {
              RAST._IType _2894_genType;
              RAST._IType _out192;
              _out192 = (this).GenType(_2893_o, false, false);
              _2894_genType = _out192;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2894_genType);
            }
          } else if (_source97.is_Tuple) {
            Dafny.ISequence<DAST._IType> _2895___mcc_h150 = _source97.dtor_Tuple_i_a0;
            DAST._IType _2896_o = _2884_t;
            {
              RAST._IType _2897_genType;
              RAST._IType _out193;
              _out193 = (this).GenType(_2896_o, false, false);
              _2897_genType = _out193;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2897_genType);
            }
          } else if (_source97.is_Array) {
            DAST._IType _2898___mcc_h152 = _source97.dtor_element;
            BigInteger _2899___mcc_h153 = _source97.dtor_dims;
            DAST._IType _2900_o = _2884_t;
            {
              RAST._IType _2901_genType;
              RAST._IType _out194;
              _out194 = (this).GenType(_2900_o, false, false);
              _2901_genType = _out194;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2901_genType);
            }
          } else if (_source97.is_Seq) {
            DAST._IType _2902___mcc_h156 = _source97.dtor_element;
            DAST._IType _2903_o = _2884_t;
            {
              RAST._IType _2904_genType;
              RAST._IType _out195;
              _out195 = (this).GenType(_2903_o, false, false);
              _2904_genType = _out195;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2904_genType);
            }
          } else if (_source97.is_Set) {
            DAST._IType _2905___mcc_h158 = _source97.dtor_element;
            DAST._IType _2906_o = _2884_t;
            {
              RAST._IType _2907_genType;
              RAST._IType _out196;
              _out196 = (this).GenType(_2906_o, false, false);
              _2907_genType = _out196;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2907_genType);
            }
          } else if (_source97.is_Multiset) {
            DAST._IType _2908___mcc_h160 = _source97.dtor_element;
            DAST._IType _2909_o = _2884_t;
            {
              RAST._IType _2910_genType;
              RAST._IType _out197;
              _out197 = (this).GenType(_2909_o, false, false);
              _2910_genType = _out197;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2910_genType);
            }
          } else if (_source97.is_Map) {
            DAST._IType _2911___mcc_h162 = _source97.dtor_key;
            DAST._IType _2912___mcc_h163 = _source97.dtor_value;
            DAST._IType _2913_o = _2884_t;
            {
              RAST._IType _2914_genType;
              RAST._IType _out198;
              _out198 = (this).GenType(_2913_o, false, false);
              _2914_genType = _out198;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2914_genType);
            }
          } else if (_source97.is_SetBuilder) {
            DAST._IType _2915___mcc_h166 = _source97.dtor_element;
            DAST._IType _2916_o = _2884_t;
            {
              RAST._IType _2917_genType;
              RAST._IType _out199;
              _out199 = (this).GenType(_2916_o, false, false);
              _2917_genType = _out199;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2917_genType);
            }
          } else if (_source97.is_MapBuilder) {
            DAST._IType _2918___mcc_h168 = _source97.dtor_key;
            DAST._IType _2919___mcc_h169 = _source97.dtor_value;
            DAST._IType _2920_o = _2884_t;
            {
              RAST._IType _2921_genType;
              RAST._IType _out200;
              _out200 = (this).GenType(_2920_o, false, false);
              _2921_genType = _out200;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2921_genType);
            }
          } else if (_source97.is_Arrow) {
            Dafny.ISequence<DAST._IType> _2922___mcc_h172 = _source97.dtor_args;
            DAST._IType _2923___mcc_h173 = _source97.dtor_result;
            DAST._IType _2924_o = _2884_t;
            {
              RAST._IType _2925_genType;
              RAST._IType _out201;
              _out201 = (this).GenType(_2924_o, false, false);
              _2925_genType = _out201;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2925_genType);
            }
          } else if (_source97.is_Primitive) {
            DAST._IPrimitive _2926___mcc_h176 = _source97.dtor_Primitive_i_a0;
            DAST._IPrimitive _source98 = _2926___mcc_h176;
            if (_source98.is_Int) {
              DAST._IType _2927_o = _2884_t;
              {
                RAST._IType _2928_genType;
                RAST._IType _out202;
                _out202 = (this).GenType(_2927_o, false, false);
                _2928_genType = _out202;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2928_genType);
              }
            } else if (_source98.is_Real) {
              {
                r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
              }
            } else if (_source98.is_String) {
              DAST._IType _2929_o = _2884_t;
              {
                RAST._IType _2930_genType;
                RAST._IType _out203;
                _out203 = (this).GenType(_2929_o, false, false);
                _2930_genType = _out203;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2930_genType);
              }
            } else if (_source98.is_Bool) {
              DAST._IType _2931_o = _2884_t;
              {
                RAST._IType _2932_genType;
                RAST._IType _out204;
                _out204 = (this).GenType(_2931_o, false, false);
                _2932_genType = _out204;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2932_genType);
              }
            } else {
              DAST._IType _2933_o = _2884_t;
              {
                RAST._IType _2934_genType;
                RAST._IType _out205;
                _out205 = (this).GenType(_2933_o, false, false);
                _2934_genType = _out205;
                r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2934_genType);
              }
            }
          } else if (_source97.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _2935___mcc_h178 = _source97.dtor_Passthrough_i_a0;
            DAST._IType _2936_o = _2884_t;
            {
              RAST._IType _2937_genType;
              RAST._IType _out206;
              _out206 = (this).GenType(_2936_o, false, false);
              _2937_genType = _out206;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2937_genType);
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _2938___mcc_h180 = _source97.dtor_TypeArg_i_a0;
            DAST._IType _2939_o = _2884_t;
            {
              RAST._IType _2940_genType;
              RAST._IType _out207;
              _out207 = (this).GenType(_2939_o, false, false);
              _2940_genType = _out207;
              r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2886_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _2885_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _2940_genType);
            }
          }
          RAST._IExpr _out208;
          DCOMP._IOwnership _out209;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out208, out _out209);
          r = _out208;
          resultingOwnership = _out209;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source94.is_StringLiteral) {
        Dafny.ISequence<Dafny.Rune> _2941___mcc_h7 = _source94.dtor_StringLiteral_i_a0;
        Dafny.ISequence<Dafny.Rune> _2942_l = _2941___mcc_h7;
        {
          r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_2942_l, false));
          RAST._IExpr _out210;
          DCOMP._IOwnership _out211;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out210, out _out211);
          r = _out210;
          resultingOwnership = _out211;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source94.is_CharLiteral) {
        Dafny.Rune _2943___mcc_h8 = _source94.dtor_CharLiteral_i_a0;
        Dafny.Rune _2944_c = _2943___mcc_h8;
        {
          r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_2944_c).Value)));
          if (!((this).UnicodeChars)) {
            r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
          } else {
            r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          }
          r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
          RAST._IExpr _out212;
          DCOMP._IOwnership _out213;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out212, out _out213);
          r = _out212;
          resultingOwnership = _out213;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else {
        DAST._IType _2945___mcc_h9 = _source94.dtor_Null_i_a0;
        DAST._IType _2946_tpe = _2945___mcc_h9;
        {
          RAST._IType _2947_tpeGen;
          RAST._IType _out214;
          _out214 = (this).GenType(_2946_tpe, false, false);
          _2947_tpeGen = _out214;
          r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None")), _2947_tpeGen);
          RAST._IExpr _out215;
          DCOMP._IOwnership _out216;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out215, out _out216);
          r = _out215;
          resultingOwnership = _out216;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      }
    }
    public void GenExprBinary(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs52 = e;
      DAST._IBinOp _2948_op = _let_tmp_rhs52.dtor_op;
      DAST._IExpression _2949_lExpr = _let_tmp_rhs52.dtor_left;
      DAST._IExpression _2950_rExpr = _let_tmp_rhs52.dtor_right;
      DAST.Format._IBinaryOpFormat _2951_format = _let_tmp_rhs52.dtor_format2;
      bool _2952_becomesLeftCallsRight;
      _2952_becomesLeftCallsRight = ((System.Func<DAST._IBinOp, bool>)((_source99) => {
        if (_source99.is_Eq) {
          bool _2953___mcc_h0 = _source99.dtor_referential;
          bool _2954___mcc_h1 = _source99.dtor_nullable;
          return false;
        } else if (_source99.is_Div) {
          return false;
        } else if (_source99.is_EuclidianDiv) {
          return false;
        } else if (_source99.is_Mod) {
          return false;
        } else if (_source99.is_EuclidianMod) {
          return false;
        } else if (_source99.is_Lt) {
          return false;
        } else if (_source99.is_LtChar) {
          return false;
        } else if (_source99.is_Plus) {
          return false;
        } else if (_source99.is_Minus) {
          return false;
        } else if (_source99.is_Times) {
          return false;
        } else if (_source99.is_BitwiseAnd) {
          return false;
        } else if (_source99.is_BitwiseOr) {
          return false;
        } else if (_source99.is_BitwiseXor) {
          return false;
        } else if (_source99.is_BitwiseShiftRight) {
          return false;
        } else if (_source99.is_BitwiseShiftLeft) {
          return false;
        } else if (_source99.is_And) {
          return false;
        } else if (_source99.is_Or) {
          return false;
        } else if (_source99.is_In) {
          return false;
        } else if (_source99.is_SeqProperPrefix) {
          return false;
        } else if (_source99.is_SeqPrefix) {
          return false;
        } else if (_source99.is_SetMerge) {
          return true;
        } else if (_source99.is_SetSubtraction) {
          return true;
        } else if (_source99.is_SetIntersection) {
          return true;
        } else if (_source99.is_Subset) {
          return false;
        } else if (_source99.is_ProperSubset) {
          return false;
        } else if (_source99.is_SetDisjoint) {
          return true;
        } else if (_source99.is_MapMerge) {
          return true;
        } else if (_source99.is_MapSubtraction) {
          return true;
        } else if (_source99.is_MultisetMerge) {
          return true;
        } else if (_source99.is_MultisetSubtraction) {
          return true;
        } else if (_source99.is_MultisetIntersection) {
          return true;
        } else if (_source99.is_Submultiset) {
          return false;
        } else if (_source99.is_ProperSubmultiset) {
          return false;
        } else if (_source99.is_MultisetDisjoint) {
          return true;
        } else if (_source99.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _2955___mcc_h4 = _source99.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2948_op);
      bool _2956_becomesRightCallsLeft;
      _2956_becomesRightCallsLeft = ((System.Func<DAST._IBinOp, bool>)((_source100) => {
        if (_source100.is_Eq) {
          bool _2957___mcc_h6 = _source100.dtor_referential;
          bool _2958___mcc_h7 = _source100.dtor_nullable;
          return false;
        } else if (_source100.is_Div) {
          return false;
        } else if (_source100.is_EuclidianDiv) {
          return false;
        } else if (_source100.is_Mod) {
          return false;
        } else if (_source100.is_EuclidianMod) {
          return false;
        } else if (_source100.is_Lt) {
          return false;
        } else if (_source100.is_LtChar) {
          return false;
        } else if (_source100.is_Plus) {
          return false;
        } else if (_source100.is_Minus) {
          return false;
        } else if (_source100.is_Times) {
          return false;
        } else if (_source100.is_BitwiseAnd) {
          return false;
        } else if (_source100.is_BitwiseOr) {
          return false;
        } else if (_source100.is_BitwiseXor) {
          return false;
        } else if (_source100.is_BitwiseShiftRight) {
          return false;
        } else if (_source100.is_BitwiseShiftLeft) {
          return false;
        } else if (_source100.is_And) {
          return false;
        } else if (_source100.is_Or) {
          return false;
        } else if (_source100.is_In) {
          return true;
        } else if (_source100.is_SeqProperPrefix) {
          return false;
        } else if (_source100.is_SeqPrefix) {
          return false;
        } else if (_source100.is_SetMerge) {
          return false;
        } else if (_source100.is_SetSubtraction) {
          return false;
        } else if (_source100.is_SetIntersection) {
          return false;
        } else if (_source100.is_Subset) {
          return false;
        } else if (_source100.is_ProperSubset) {
          return false;
        } else if (_source100.is_SetDisjoint) {
          return false;
        } else if (_source100.is_MapMerge) {
          return false;
        } else if (_source100.is_MapSubtraction) {
          return false;
        } else if (_source100.is_MultisetMerge) {
          return false;
        } else if (_source100.is_MultisetSubtraction) {
          return false;
        } else if (_source100.is_MultisetIntersection) {
          return false;
        } else if (_source100.is_Submultiset) {
          return false;
        } else if (_source100.is_ProperSubmultiset) {
          return false;
        } else if (_source100.is_MultisetDisjoint) {
          return false;
        } else if (_source100.is_Concat) {
          return false;
        } else {
          Dafny.ISequence<Dafny.Rune> _2959___mcc_h10 = _source100.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2948_op);
      bool _2960_becomesCallLeftRight;
      _2960_becomesCallLeftRight = ((System.Func<DAST._IBinOp, bool>)((_source101) => {
        if (_source101.is_Eq) {
          bool _2961___mcc_h12 = _source101.dtor_referential;
          bool _2962___mcc_h13 = _source101.dtor_nullable;
          if ((_2961___mcc_h12) == (true)) {
            if ((_2962___mcc_h13) == (false)) {
              return true;
            } else {
              return false;
            }
          } else {
            return false;
          }
        } else if (_source101.is_Div) {
          return false;
        } else if (_source101.is_EuclidianDiv) {
          return false;
        } else if (_source101.is_Mod) {
          return false;
        } else if (_source101.is_EuclidianMod) {
          return false;
        } else if (_source101.is_Lt) {
          return false;
        } else if (_source101.is_LtChar) {
          return false;
        } else if (_source101.is_Plus) {
          return false;
        } else if (_source101.is_Minus) {
          return false;
        } else if (_source101.is_Times) {
          return false;
        } else if (_source101.is_BitwiseAnd) {
          return false;
        } else if (_source101.is_BitwiseOr) {
          return false;
        } else if (_source101.is_BitwiseXor) {
          return false;
        } else if (_source101.is_BitwiseShiftRight) {
          return false;
        } else if (_source101.is_BitwiseShiftLeft) {
          return false;
        } else if (_source101.is_And) {
          return false;
        } else if (_source101.is_Or) {
          return false;
        } else if (_source101.is_In) {
          return false;
        } else if (_source101.is_SeqProperPrefix) {
          return false;
        } else if (_source101.is_SeqPrefix) {
          return false;
        } else if (_source101.is_SetMerge) {
          return true;
        } else if (_source101.is_SetSubtraction) {
          return true;
        } else if (_source101.is_SetIntersection) {
          return true;
        } else if (_source101.is_Subset) {
          return false;
        } else if (_source101.is_ProperSubset) {
          return false;
        } else if (_source101.is_SetDisjoint) {
          return true;
        } else if (_source101.is_MapMerge) {
          return true;
        } else if (_source101.is_MapSubtraction) {
          return true;
        } else if (_source101.is_MultisetMerge) {
          return true;
        } else if (_source101.is_MultisetSubtraction) {
          return true;
        } else if (_source101.is_MultisetIntersection) {
          return true;
        } else if (_source101.is_Submultiset) {
          return false;
        } else if (_source101.is_ProperSubmultiset) {
          return false;
        } else if (_source101.is_MultisetDisjoint) {
          return true;
        } else if (_source101.is_Concat) {
          return true;
        } else {
          Dafny.ISequence<Dafny.Rune> _2963___mcc_h16 = _source101.dtor_Passthrough_i_a0;
          return false;
        }
      }))(_2948_op);
      DCOMP._IOwnership _2964_expectedLeftOwnership;
      _2964_expectedLeftOwnership = ((_2952_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_2956_becomesRightCallsLeft) || (_2960_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _2965_expectedRightOwnership;
      _2965_expectedRightOwnership = (((_2952_becomesLeftCallsRight) || (_2960_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_2956_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _2966_left;
      DCOMP._IOwnership _2967___v74;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2968_recIdentsL;
      RAST._IExpr _out217;
      DCOMP._IOwnership _out218;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out219;
      (this).GenExpr(_2949_lExpr, selfIdent, env, _2964_expectedLeftOwnership, out _out217, out _out218, out _out219);
      _2966_left = _out217;
      _2967___v74 = _out218;
      _2968_recIdentsL = _out219;
      RAST._IExpr _2969_right;
      DCOMP._IOwnership _2970___v75;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2971_recIdentsR;
      RAST._IExpr _out220;
      DCOMP._IOwnership _out221;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out222;
      (this).GenExpr(_2950_rExpr, selfIdent, env, _2965_expectedRightOwnership, out _out220, out _out221, out _out222);
      _2969_right = _out220;
      _2970___v75 = _out221;
      _2971_recIdentsR = _out222;
      DAST._IBinOp _source102 = _2948_op;
      if (_source102.is_Eq) {
        bool _2972___mcc_h18 = _source102.dtor_referential;
        bool _2973___mcc_h19 = _source102.dtor_nullable;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source103 = _2948_op;
            if (_source103.is_Eq) {
              bool _2974___mcc_h24 = _source103.dtor_referential;
              bool _2975___mcc_h25 = _source103.dtor_nullable;
              bool _2976_nullable = _2975___mcc_h25;
              bool _2977_referential = _2974___mcc_h24;
              {
                if (_2977_referential) {
                  if (_2976_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source103.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source103.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2978___mcc_h26 = _source103.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _2979_op = _2978___mcc_h26;
              {
                r = RAST.Expr.create_BinaryOp(_2979_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_Div) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source104 = _2948_op;
            if (_source104.is_Eq) {
              bool _2980___mcc_h27 = _source104.dtor_referential;
              bool _2981___mcc_h28 = _source104.dtor_nullable;
              bool _2982_nullable = _2981___mcc_h28;
              bool _2983_referential = _2980___mcc_h27;
              {
                if (_2983_referential) {
                  if (_2982_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source104.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source104.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2984___mcc_h29 = _source104.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _2985_op = _2984___mcc_h29;
              {
                r = RAST.Expr.create_BinaryOp(_2985_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_EuclidianDiv) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source105 = _2948_op;
            if (_source105.is_Eq) {
              bool _2986___mcc_h30 = _source105.dtor_referential;
              bool _2987___mcc_h31 = _source105.dtor_nullable;
              bool _2988_nullable = _2987___mcc_h31;
              bool _2989_referential = _2986___mcc_h30;
              {
                if (_2989_referential) {
                  if (_2988_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source105.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source105.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2990___mcc_h32 = _source105.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _2991_op = _2990___mcc_h32;
              {
                r = RAST.Expr.create_BinaryOp(_2991_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_Mod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source106 = _2948_op;
            if (_source106.is_Eq) {
              bool _2992___mcc_h33 = _source106.dtor_referential;
              bool _2993___mcc_h34 = _source106.dtor_nullable;
              bool _2994_nullable = _2993___mcc_h34;
              bool _2995_referential = _2992___mcc_h33;
              {
                if (_2995_referential) {
                  if (_2994_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source106.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source106.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _2996___mcc_h35 = _source106.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _2997_op = _2996___mcc_h35;
              {
                r = RAST.Expr.create_BinaryOp(_2997_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_EuclidianMod) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source107 = _2948_op;
            if (_source107.is_Eq) {
              bool _2998___mcc_h36 = _source107.dtor_referential;
              bool _2999___mcc_h37 = _source107.dtor_nullable;
              bool _3000_nullable = _2999___mcc_h37;
              bool _3001_referential = _2998___mcc_h36;
              {
                if (_3001_referential) {
                  if (_3000_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source107.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source107.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3002___mcc_h38 = _source107.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3003_op = _3002___mcc_h38;
              {
                r = RAST.Expr.create_BinaryOp(_3003_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_Lt) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source108 = _2948_op;
            if (_source108.is_Eq) {
              bool _3004___mcc_h39 = _source108.dtor_referential;
              bool _3005___mcc_h40 = _source108.dtor_nullable;
              bool _3006_nullable = _3005___mcc_h40;
              bool _3007_referential = _3004___mcc_h39;
              {
                if (_3007_referential) {
                  if (_3006_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source108.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source108.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3008___mcc_h41 = _source108.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3009_op = _3008___mcc_h41;
              {
                r = RAST.Expr.create_BinaryOp(_3009_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_LtChar) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source109 = _2948_op;
            if (_source109.is_Eq) {
              bool _3010___mcc_h42 = _source109.dtor_referential;
              bool _3011___mcc_h43 = _source109.dtor_nullable;
              bool _3012_nullable = _3011___mcc_h43;
              bool _3013_referential = _3010___mcc_h42;
              {
                if (_3013_referential) {
                  if (_3012_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source109.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source109.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3014___mcc_h44 = _source109.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3015_op = _3014___mcc_h44;
              {
                r = RAST.Expr.create_BinaryOp(_3015_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_Plus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source110 = _2948_op;
            if (_source110.is_Eq) {
              bool _3016___mcc_h45 = _source110.dtor_referential;
              bool _3017___mcc_h46 = _source110.dtor_nullable;
              bool _3018_nullable = _3017___mcc_h46;
              bool _3019_referential = _3016___mcc_h45;
              {
                if (_3019_referential) {
                  if (_3018_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source110.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source110.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3020___mcc_h47 = _source110.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3021_op = _3020___mcc_h47;
              {
                r = RAST.Expr.create_BinaryOp(_3021_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_Minus) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source111 = _2948_op;
            if (_source111.is_Eq) {
              bool _3022___mcc_h48 = _source111.dtor_referential;
              bool _3023___mcc_h49 = _source111.dtor_nullable;
              bool _3024_nullable = _3023___mcc_h49;
              bool _3025_referential = _3022___mcc_h48;
              {
                if (_3025_referential) {
                  if (_3024_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source111.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source111.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3026___mcc_h50 = _source111.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3027_op = _3026___mcc_h50;
              {
                r = RAST.Expr.create_BinaryOp(_3027_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_Times) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source112 = _2948_op;
            if (_source112.is_Eq) {
              bool _3028___mcc_h51 = _source112.dtor_referential;
              bool _3029___mcc_h52 = _source112.dtor_nullable;
              bool _3030_nullable = _3029___mcc_h52;
              bool _3031_referential = _3028___mcc_h51;
              {
                if (_3031_referential) {
                  if (_3030_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source112.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source112.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3032___mcc_h53 = _source112.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3033_op = _3032___mcc_h53;
              {
                r = RAST.Expr.create_BinaryOp(_3033_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_BitwiseAnd) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source113 = _2948_op;
            if (_source113.is_Eq) {
              bool _3034___mcc_h54 = _source113.dtor_referential;
              bool _3035___mcc_h55 = _source113.dtor_nullable;
              bool _3036_nullable = _3035___mcc_h55;
              bool _3037_referential = _3034___mcc_h54;
              {
                if (_3037_referential) {
                  if (_3036_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source113.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source113.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3038___mcc_h56 = _source113.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3039_op = _3038___mcc_h56;
              {
                r = RAST.Expr.create_BinaryOp(_3039_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_BitwiseOr) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source114 = _2948_op;
            if (_source114.is_Eq) {
              bool _3040___mcc_h57 = _source114.dtor_referential;
              bool _3041___mcc_h58 = _source114.dtor_nullable;
              bool _3042_nullable = _3041___mcc_h58;
              bool _3043_referential = _3040___mcc_h57;
              {
                if (_3043_referential) {
                  if (_3042_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source114.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source114.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3044___mcc_h59 = _source114.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3045_op = _3044___mcc_h59;
              {
                r = RAST.Expr.create_BinaryOp(_3045_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_BitwiseXor) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source115 = _2948_op;
            if (_source115.is_Eq) {
              bool _3046___mcc_h60 = _source115.dtor_referential;
              bool _3047___mcc_h61 = _source115.dtor_nullable;
              bool _3048_nullable = _3047___mcc_h61;
              bool _3049_referential = _3046___mcc_h60;
              {
                if (_3049_referential) {
                  if (_3048_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source115.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source115.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3050___mcc_h62 = _source115.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3051_op = _3050___mcc_h62;
              {
                r = RAST.Expr.create_BinaryOp(_3051_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_BitwiseShiftRight) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source116 = _2948_op;
            if (_source116.is_Eq) {
              bool _3052___mcc_h63 = _source116.dtor_referential;
              bool _3053___mcc_h64 = _source116.dtor_nullable;
              bool _3054_nullable = _3053___mcc_h64;
              bool _3055_referential = _3052___mcc_h63;
              {
                if (_3055_referential) {
                  if (_3054_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source116.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source116.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3056___mcc_h65 = _source116.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3057_op = _3056___mcc_h65;
              {
                r = RAST.Expr.create_BinaryOp(_3057_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_BitwiseShiftLeft) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source117 = _2948_op;
            if (_source117.is_Eq) {
              bool _3058___mcc_h66 = _source117.dtor_referential;
              bool _3059___mcc_h67 = _source117.dtor_nullable;
              bool _3060_nullable = _3059___mcc_h67;
              bool _3061_referential = _3058___mcc_h66;
              {
                if (_3061_referential) {
                  if (_3060_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source117.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source117.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3062___mcc_h68 = _source117.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3063_op = _3062___mcc_h68;
              {
                r = RAST.Expr.create_BinaryOp(_3063_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_And) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source118 = _2948_op;
            if (_source118.is_Eq) {
              bool _3064___mcc_h69 = _source118.dtor_referential;
              bool _3065___mcc_h70 = _source118.dtor_nullable;
              bool _3066_nullable = _3065___mcc_h70;
              bool _3067_referential = _3064___mcc_h69;
              {
                if (_3067_referential) {
                  if (_3066_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source118.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source118.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3068___mcc_h71 = _source118.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3069_op = _3068___mcc_h71;
              {
                r = RAST.Expr.create_BinaryOp(_3069_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_Or) {
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source119 = _2948_op;
            if (_source119.is_Eq) {
              bool _3070___mcc_h72 = _source119.dtor_referential;
              bool _3071___mcc_h73 = _source119.dtor_nullable;
              bool _3072_nullable = _3071___mcc_h73;
              bool _3073_referential = _3070___mcc_h72;
              {
                if (_3073_referential) {
                  if (_3072_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source119.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source119.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3074___mcc_h74 = _source119.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3075_op = _3074___mcc_h74;
              {
                r = RAST.Expr.create_BinaryOp(_3075_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      } else if (_source102.is_In) {
        {
          r = ((_2969_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_2966_left);
        }
      } else if (_source102.is_SeqProperPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2966_left, _2969_right, _2951_format);
      } else if (_source102.is_SeqPrefix) {
        r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2966_left, _2969_right, _2951_format);
      } else if (_source102.is_SetMerge) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2969_right);
        }
      } else if (_source102.is_SetSubtraction) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2969_right);
        }
      } else if (_source102.is_SetIntersection) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2969_right);
        }
      } else if (_source102.is_Subset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2966_left, _2969_right, _2951_format);
        }
      } else if (_source102.is_ProperSubset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2966_left, _2969_right, _2951_format);
        }
      } else if (_source102.is_SetDisjoint) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2969_right);
        }
      } else if (_source102.is_MapMerge) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2969_right);
        }
      } else if (_source102.is_MapSubtraction) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2969_right);
        }
      } else if (_source102.is_MultisetMerge) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_2969_right);
        }
      } else if (_source102.is_MultisetSubtraction) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_2969_right);
        }
      } else if (_source102.is_MultisetIntersection) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_2969_right);
        }
      } else if (_source102.is_Submultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _2966_left, _2969_right, _2951_format);
        }
      } else if (_source102.is_ProperSubmultiset) {
        {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2966_left, _2969_right, _2951_format);
        }
      } else if (_source102.is_MultisetDisjoint) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_2969_right);
        }
      } else if (_source102.is_Concat) {
        {
          r = ((_2966_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_2969_right);
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _3076___mcc_h22 = _source102.dtor_Passthrough_i_a0;
        {
          if ((DCOMP.COMP.OpTable).Contains(_2948_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_2948_op), _2966_left, _2969_right, _2951_format);
          } else {
            DAST._IBinOp _source120 = _2948_op;
            if (_source120.is_Eq) {
              bool _3077___mcc_h75 = _source120.dtor_referential;
              bool _3078___mcc_h76 = _source120.dtor_nullable;
              bool _3079_nullable = _3078___mcc_h76;
              bool _3080_referential = _3077___mcc_h75;
              {
                if (_3080_referential) {
                  if (_3079_nullable) {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::nullable_referential_equality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  } else {
                    r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::ptr_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
                  }
                } else {
                  r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _2966_left, _2969_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                }
              }
            } else if (_source120.is_EuclidianDiv) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else if (_source120.is_EuclidianMod) {
              {
                r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2966_left, _2969_right));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3081___mcc_h77 = _source120.dtor_Passthrough_i_a0;
              Dafny.ISequence<Dafny.Rune> _3082_op = _3081___mcc_h77;
              {
                r = RAST.Expr.create_BinaryOp(_3082_op, _2966_left, _2969_right, _2951_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out223;
      DCOMP._IOwnership _out224;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out223, out _out224);
      r = _out223;
      resultingOwnership = _out224;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2968_recIdentsL, _2971_recIdentsR);
      return ;
    }
    public void GenExprConvertFromNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IExpression _3083_expr = _let_tmp_rhs53.dtor_value;
      DAST._IType _3084_fromTpe = _let_tmp_rhs53.dtor_from;
      DAST._IType _3085_toTpe = _let_tmp_rhs53.dtor_typ;
      RAST._IExpr _3086_recursiveGen;
      DCOMP._IOwnership _3087_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3088_recIdents;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_3083_expr, selfIdent, env, expectedOwnership, out _out225, out _out226, out _out227);
      _3086_recursiveGen = _out225;
      _3087_recOwned = _out226;
      _3088_recIdents = _out227;
      r = _3086_recursiveGen;
      if (object.Equals(_3087_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      RAST._IExpr _out228;
      DCOMP._IOwnership _out229;
      DCOMP.COMP.FromOwnership(r, _3087_recOwned, expectedOwnership, out _out228, out _out229);
      r = _out228;
      resultingOwnership = _out229;
      readIdents = _3088_recIdents;
    }
    public void GenExprConvertToNullable(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _3089_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _3090_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _3091_toTpe = _let_tmp_rhs54.dtor_typ;
      RAST._IExpr _3092_recursiveGen;
      DCOMP._IOwnership _3093_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3094_recIdents;
      RAST._IExpr _out230;
      DCOMP._IOwnership _out231;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
      (this).GenExpr(_3089_expr, selfIdent, env, expectedOwnership, out _out230, out _out231, out _out232);
      _3092_recursiveGen = _out230;
      _3093_recOwned = _out231;
      _3094_recIdents = _out232;
      r = _3092_recursiveGen;
      if (object.Equals(_3093_recOwned, DCOMP.Ownership.create_OwnershipOwned())) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
      RAST._IExpr _out233;
      DCOMP._IOwnership _out234;
      DCOMP.COMP.FromOwnership(r, _3093_recOwned, expectedOwnership, out _out233, out _out234);
      r = _out233;
      resultingOwnership = _out234;
      readIdents = _3094_recIdents;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _3095_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _3096_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _3097_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _3097_toTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3098___v77 = _let_tmp_rhs56.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _3099___v78 = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      DAST._IType _3100_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _3101_range = _let_tmp_rhs57.dtor_range;
      bool _3102_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _3103_attributes = _let_tmp_rhs57.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _3104_nativeToType;
      _3104_nativeToType = DCOMP.COMP.NewtypeToRustType(_3100_b, _3101_range);
      if (object.Equals(_3096_fromTpe, _3100_b)) {
        RAST._IExpr _3105_recursiveGen;
        DCOMP._IOwnership _3106_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3107_recIdents;
        RAST._IExpr _out235;
        DCOMP._IOwnership _out236;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out237;
        (this).GenExpr(_3095_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out235, out _out236, out _out237);
        _3105_recursiveGen = _out235;
        _3106_recOwned = _out236;
        _3107_recIdents = _out237;
        readIdents = _3107_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source121 = _3104_nativeToType;
        if (_source121.is_None) {
          if (_3102_erase) {
            r = _3105_recursiveGen;
          } else {
            RAST._IType _3108_rhsType;
            RAST._IType _out238;
            _out238 = (this).GenType(_3097_toTpe, true, false);
            _3108_rhsType = _out238;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_3108_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_3105_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out239;
          DCOMP._IOwnership _out240;
          DCOMP.COMP.FromOwnership(r, _3106_recOwned, expectedOwnership, out _out239, out _out240);
          r = _out239;
          resultingOwnership = _out240;
        } else {
          RAST._IType _3109___mcc_h0 = _source121.dtor_value;
          RAST._IType _3110_v = _3109___mcc_h0;
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_3105_recursiveGen, RAST.Expr.create_ExprFromType(_3110_v)));
          RAST._IExpr _out241;
          DCOMP._IOwnership _out242;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out241, out _out242);
          r = _out241;
          resultingOwnership = _out242;
        }
      } else {
        RAST._IExpr _out243;
        DCOMP._IOwnership _out244;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_3095_expr, _3096_fromTpe, _3100_b), _3100_b, _3097_toTpe), selfIdent, env, expectedOwnership, out _out243, out _out244, out _out245);
        r = _out243;
        resultingOwnership = _out244;
        readIdents = _out245;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _3111_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _3112_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _3113_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _3112_fromTpe;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3114___v79 = _let_tmp_rhs59.dtor_Path_i_a0;
      Dafny.ISequence<DAST._IType> _3115___v80 = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      DAST._IType _3116_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _3117_range = _let_tmp_rhs60.dtor_range;
      bool _3118_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _3119_attributes = _let_tmp_rhs60.dtor_attributes;
      Std.Wrappers._IOption<RAST._IType> _3120_nativeFromType;
      _3120_nativeFromType = DCOMP.COMP.NewtypeToRustType(_3116_b, _3117_range);
      if (object.Equals(_3116_b, _3113_toTpe)) {
        RAST._IExpr _3121_recursiveGen;
        DCOMP._IOwnership _3122_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3123_recIdents;
        RAST._IExpr _out246;
        DCOMP._IOwnership _out247;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out248;
        (this).GenExpr(_3111_expr, selfIdent, env, expectedOwnership, out _out246, out _out247, out _out248);
        _3121_recursiveGen = _out246;
        _3122_recOwned = _out247;
        _3123_recIdents = _out248;
        readIdents = _3123_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source122 = _3120_nativeFromType;
        if (_source122.is_None) {
          if (_3118_erase) {
            r = _3121_recursiveGen;
          } else {
            r = (_3121_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out249;
          DCOMP._IOwnership _out250;
          DCOMP.COMP.FromOwnership(r, _3122_recOwned, expectedOwnership, out _out249, out _out250);
          r = _out249;
          resultingOwnership = _out250;
        } else {
          RAST._IType _3124___mcc_h0 = _source122.dtor_value;
          RAST._IType _3125_v = _3124___mcc_h0;
          RAST._IType _3126_toTpeRust;
          RAST._IType _out251;
          _out251 = (this).GenType(_3113_toTpe, false, false);
          _3126_toTpeRust = _out251;
          r = (((_3121_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_3126_toTpeRust))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out252;
          DCOMP._IOwnership _out253;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out252, out _out253);
          r = _out252;
          resultingOwnership = _out253;
        }
      } else {
        if ((_3120_nativeFromType).is_Some) {
          if (object.Equals(_3113_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _3127_recursiveGen;
            DCOMP._IOwnership _3128_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3129_recIdents;
            RAST._IExpr _out254;
            DCOMP._IOwnership _out255;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out256;
            (this).GenExpr(_3111_expr, selfIdent, env, expectedOwnership, out _out254, out _out255, out _out256);
            _3127_recursiveGen = _out254;
            _3128_recOwned = _out255;
            _3129_recIdents = _out256;
            RAST._IExpr _out257;
            DCOMP._IOwnership _out258;
            DCOMP.COMP.FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_3127_recursiveGen, (this).DafnyCharUnderlying)), _3128_recOwned, expectedOwnership, out _out257, out _out258);
            r = _out257;
            resultingOwnership = _out258;
            readIdents = _3129_recIdents;
            return ;
          }
        }
        RAST._IExpr _out259;
        DCOMP._IOwnership _out260;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_3111_expr, _3112_fromTpe, _3116_b), _3116_b, _3113_toTpe), selfIdent, env, expectedOwnership, out _out259, out _out260, out _out261);
        r = _out259;
        resultingOwnership = _out260;
        readIdents = _out261;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _3130_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _3131_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _3132_toTpe = _let_tmp_rhs61.dtor_typ;
      RAST._IType _3133_fromTpeGen;
      RAST._IType _out262;
      _out262 = (this).GenType(_3131_fromTpe, true, false);
      _3133_fromTpeGen = _out262;
      RAST._IType _3134_toTpeGen;
      RAST._IType _out263;
      _out263 = (this).GenType(_3132_toTpe, true, false);
      _3134_toTpeGen = _out263;
      RAST._IExpr _3135_recursiveGen;
      DCOMP._IOwnership _3136_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3137_recIdents;
      RAST._IExpr _out264;
      DCOMP._IOwnership _out265;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
      (this).GenExpr(_3130_expr, selfIdent, env, expectedOwnership, out _out264, out _out265, out _out266);
      _3135_recursiveGen = _out264;
      _3136_recOwned = _out265;
      _3137_recIdents = _out266;
      Dafny.ISequence<Dafny.Rune> _3138_msg;
      _3138_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_3133_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_3134_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_3138_msg);
      r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_3135_recursiveGen)._ToString(DCOMP.__default.IND), _3138_msg));
      RAST._IExpr _out267;
      DCOMP._IOwnership _out268;
      DCOMP.COMP.FromOwned(r, expectedOwnership, out _out267, out _out268);
      r = _out267;
      resultingOwnership = _out268;
      readIdents = _3137_recIdents;
    }
    public void GenExprConvert(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _3139_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _3140_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _3141_toTpe = _let_tmp_rhs62.dtor_typ;
      if (object.Equals(_3140_fromTpe, _3141_toTpe)) {
        RAST._IExpr _3142_recursiveGen;
        DCOMP._IOwnership _3143_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3144_recIdents;
        RAST._IExpr _out269;
        DCOMP._IOwnership _out270;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
        (this).GenExpr(_3139_expr, selfIdent, env, expectedOwnership, out _out269, out _out270, out _out271);
        _3142_recursiveGen = _out269;
        _3143_recOwned = _out270;
        _3144_recIdents = _out271;
        r = _3142_recursiveGen;
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        DCOMP.COMP.FromOwnership(r, _3143_recOwned, expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
        readIdents = _3144_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source123 = _System.Tuple2<DAST._IType, DAST._IType>.create(_3140_fromTpe, _3141_toTpe);
        DAST._IType _3145___mcc_h0 = _source123.dtor__0;
        DAST._IType _3146___mcc_h1 = _source123.dtor__1;
        DAST._IType _source124 = _3145___mcc_h0;
        if (_source124.is_Path) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3147___mcc_h4 = _source124.dtor_Path_i_a0;
          Dafny.ISequence<DAST._IType> _3148___mcc_h5 = _source124.dtor_typeArgs;
          DAST._IResolvedType _3149___mcc_h6 = _source124.dtor_resolved;
          DAST._IResolvedType _source125 = _3149___mcc_h6;
          if (_source125.is_Datatype) {
            DAST._IDatatypeType _3150___mcc_h16 = _source125.dtor_datatypeType;
            DAST._IType _source126 = _3146___mcc_h1;
            if (_source126.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3151___mcc_h20 = _source126.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3152___mcc_h21 = _source126.dtor_typeArgs;
              DAST._IResolvedType _3153___mcc_h22 = _source126.dtor_resolved;
              DAST._IResolvedType _source127 = _3153___mcc_h22;
              if (_source127.is_Datatype) {
                DAST._IDatatypeType _3154___mcc_h26 = _source127.dtor_datatypeType;
                {
                  RAST._IExpr _out274;
                  DCOMP._IOwnership _out275;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out274, out _out275, out _out276);
                  r = _out274;
                  resultingOwnership = _out275;
                  readIdents = _out276;
                }
              } else if (_source127.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3155___mcc_h28 = _source127.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3156___mcc_h29 = _source127.dtor_attributes;
                {
                  RAST._IExpr _out277;
                  DCOMP._IOwnership _out278;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out279;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out277, out _out278, out _out279);
                  r = _out277;
                  resultingOwnership = _out278;
                  readIdents = _out279;
                }
              } else {
                DAST._IType _3157___mcc_h32 = _source127.dtor_baseType;
                DAST._INewtypeRange _3158___mcc_h33 = _source127.dtor_range;
                bool _3159___mcc_h34 = _source127.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3160___mcc_h35 = _source127.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3161_attributes = _3160___mcc_h35;
                bool _3162_erase = _3159___mcc_h34;
                DAST._INewtypeRange _3163_range = _3158___mcc_h33;
                DAST._IType _3164_b = _3157___mcc_h32;
                {
                  RAST._IExpr _out280;
                  DCOMP._IOwnership _out281;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out280, out _out281, out _out282);
                  r = _out280;
                  resultingOwnership = _out281;
                  readIdents = _out282;
                }
              }
            } else if (_source126.is_Nullable) {
              DAST._IType _3165___mcc_h40 = _source126.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out283;
                DCOMP._IOwnership _out284;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out283, out _out284, out _out285);
                r = _out283;
                resultingOwnership = _out284;
                readIdents = _out285;
              }
            } else if (_source126.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3166___mcc_h42 = _source126.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out286;
                DCOMP._IOwnership _out287;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out288;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out286, out _out287, out _out288);
                r = _out286;
                resultingOwnership = _out287;
                readIdents = _out288;
              }
            } else if (_source126.is_Array) {
              DAST._IType _3167___mcc_h44 = _source126.dtor_element;
              BigInteger _3168___mcc_h45 = _source126.dtor_dims;
              {
                RAST._IExpr _out289;
                DCOMP._IOwnership _out290;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out291;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out289, out _out290, out _out291);
                r = _out289;
                resultingOwnership = _out290;
                readIdents = _out291;
              }
            } else if (_source126.is_Seq) {
              DAST._IType _3169___mcc_h48 = _source126.dtor_element;
              {
                RAST._IExpr _out292;
                DCOMP._IOwnership _out293;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out292, out _out293, out _out294);
                r = _out292;
                resultingOwnership = _out293;
                readIdents = _out294;
              }
            } else if (_source126.is_Set) {
              DAST._IType _3170___mcc_h50 = _source126.dtor_element;
              {
                RAST._IExpr _out295;
                DCOMP._IOwnership _out296;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out295, out _out296, out _out297);
                r = _out295;
                resultingOwnership = _out296;
                readIdents = _out297;
              }
            } else if (_source126.is_Multiset) {
              DAST._IType _3171___mcc_h52 = _source126.dtor_element;
              {
                RAST._IExpr _out298;
                DCOMP._IOwnership _out299;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out300;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out298, out _out299, out _out300);
                r = _out298;
                resultingOwnership = _out299;
                readIdents = _out300;
              }
            } else if (_source126.is_Map) {
              DAST._IType _3172___mcc_h54 = _source126.dtor_key;
              DAST._IType _3173___mcc_h55 = _source126.dtor_value;
              {
                RAST._IExpr _out301;
                DCOMP._IOwnership _out302;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out301, out _out302, out _out303);
                r = _out301;
                resultingOwnership = _out302;
                readIdents = _out303;
              }
            } else if (_source126.is_SetBuilder) {
              DAST._IType _3174___mcc_h58 = _source126.dtor_element;
              {
                RAST._IExpr _out304;
                DCOMP._IOwnership _out305;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out306;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out304, out _out305, out _out306);
                r = _out304;
                resultingOwnership = _out305;
                readIdents = _out306;
              }
            } else if (_source126.is_MapBuilder) {
              DAST._IType _3175___mcc_h60 = _source126.dtor_key;
              DAST._IType _3176___mcc_h61 = _source126.dtor_value;
              {
                RAST._IExpr _out307;
                DCOMP._IOwnership _out308;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out309;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out307, out _out308, out _out309);
                r = _out307;
                resultingOwnership = _out308;
                readIdents = _out309;
              }
            } else if (_source126.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3177___mcc_h64 = _source126.dtor_args;
              DAST._IType _3178___mcc_h65 = _source126.dtor_result;
              {
                RAST._IExpr _out310;
                DCOMP._IOwnership _out311;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out312;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out310, out _out311, out _out312);
                r = _out310;
                resultingOwnership = _out311;
                readIdents = _out312;
              }
            } else if (_source126.is_Primitive) {
              DAST._IPrimitive _3179___mcc_h68 = _source126.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out313;
                DCOMP._IOwnership _out314;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out313, out _out314, out _out315);
                r = _out313;
                resultingOwnership = _out314;
                readIdents = _out315;
              }
            } else if (_source126.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3180___mcc_h70 = _source126.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out316;
                DCOMP._IOwnership _out317;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out316, out _out317, out _out318);
                r = _out316;
                resultingOwnership = _out317;
                readIdents = _out318;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3181___mcc_h72 = _source126.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out319;
                DCOMP._IOwnership _out320;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out321;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out319, out _out320, out _out321);
                r = _out319;
                resultingOwnership = _out320;
                readIdents = _out321;
              }
            }
          } else if (_source125.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3182___mcc_h74 = _source125.dtor_path;
            Dafny.ISequence<DAST._IAttribute> _3183___mcc_h75 = _source125.dtor_attributes;
            DAST._IType _source128 = _3146___mcc_h1;
            if (_source128.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3184___mcc_h82 = _source128.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3185___mcc_h83 = _source128.dtor_typeArgs;
              DAST._IResolvedType _3186___mcc_h84 = _source128.dtor_resolved;
              DAST._IResolvedType _source129 = _3186___mcc_h84;
              if (_source129.is_Datatype) {
                DAST._IDatatypeType _3187___mcc_h88 = _source129.dtor_datatypeType;
                {
                  RAST._IExpr _out322;
                  DCOMP._IOwnership _out323;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out322, out _out323, out _out324);
                  r = _out322;
                  resultingOwnership = _out323;
                  readIdents = _out324;
                }
              } else if (_source129.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3188___mcc_h90 = _source129.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3189___mcc_h91 = _source129.dtor_attributes;
                {
                  RAST._IExpr _out325;
                  DCOMP._IOwnership _out326;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out325, out _out326, out _out327);
                  r = _out325;
                  resultingOwnership = _out326;
                  readIdents = _out327;
                }
              } else {
                DAST._IType _3190___mcc_h94 = _source129.dtor_baseType;
                DAST._INewtypeRange _3191___mcc_h95 = _source129.dtor_range;
                bool _3192___mcc_h96 = _source129.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3193___mcc_h97 = _source129.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3194_attributes = _3193___mcc_h97;
                bool _3195_erase = _3192___mcc_h96;
                DAST._INewtypeRange _3196_range = _3191___mcc_h95;
                DAST._IType _3197_b = _3190___mcc_h94;
                {
                  RAST._IExpr _out328;
                  DCOMP._IOwnership _out329;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out330;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out328, out _out329, out _out330);
                  r = _out328;
                  resultingOwnership = _out329;
                  readIdents = _out330;
                }
              }
            } else if (_source128.is_Nullable) {
              DAST._IType _3198___mcc_h102 = _source128.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out331;
                DCOMP._IOwnership _out332;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out333;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out331, out _out332, out _out333);
                r = _out331;
                resultingOwnership = _out332;
                readIdents = _out333;
              }
            } else if (_source128.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3199___mcc_h104 = _source128.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out334;
                DCOMP._IOwnership _out335;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out336;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out334, out _out335, out _out336);
                r = _out334;
                resultingOwnership = _out335;
                readIdents = _out336;
              }
            } else if (_source128.is_Array) {
              DAST._IType _3200___mcc_h106 = _source128.dtor_element;
              BigInteger _3201___mcc_h107 = _source128.dtor_dims;
              {
                RAST._IExpr _out337;
                DCOMP._IOwnership _out338;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out337, out _out338, out _out339);
                r = _out337;
                resultingOwnership = _out338;
                readIdents = _out339;
              }
            } else if (_source128.is_Seq) {
              DAST._IType _3202___mcc_h110 = _source128.dtor_element;
              {
                RAST._IExpr _out340;
                DCOMP._IOwnership _out341;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out342;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out340, out _out341, out _out342);
                r = _out340;
                resultingOwnership = _out341;
                readIdents = _out342;
              }
            } else if (_source128.is_Set) {
              DAST._IType _3203___mcc_h112 = _source128.dtor_element;
              {
                RAST._IExpr _out343;
                DCOMP._IOwnership _out344;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out343, out _out344, out _out345);
                r = _out343;
                resultingOwnership = _out344;
                readIdents = _out345;
              }
            } else if (_source128.is_Multiset) {
              DAST._IType _3204___mcc_h114 = _source128.dtor_element;
              {
                RAST._IExpr _out346;
                DCOMP._IOwnership _out347;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
                r = _out346;
                resultingOwnership = _out347;
                readIdents = _out348;
              }
            } else if (_source128.is_Map) {
              DAST._IType _3205___mcc_h116 = _source128.dtor_key;
              DAST._IType _3206___mcc_h117 = _source128.dtor_value;
              {
                RAST._IExpr _out349;
                DCOMP._IOwnership _out350;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out349, out _out350, out _out351);
                r = _out349;
                resultingOwnership = _out350;
                readIdents = _out351;
              }
            } else if (_source128.is_SetBuilder) {
              DAST._IType _3207___mcc_h120 = _source128.dtor_element;
              {
                RAST._IExpr _out352;
                DCOMP._IOwnership _out353;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out354;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out352, out _out353, out _out354);
                r = _out352;
                resultingOwnership = _out353;
                readIdents = _out354;
              }
            } else if (_source128.is_MapBuilder) {
              DAST._IType _3208___mcc_h122 = _source128.dtor_key;
              DAST._IType _3209___mcc_h123 = _source128.dtor_value;
              {
                RAST._IExpr _out355;
                DCOMP._IOwnership _out356;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out357;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out355, out _out356, out _out357);
                r = _out355;
                resultingOwnership = _out356;
                readIdents = _out357;
              }
            } else if (_source128.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3210___mcc_h126 = _source128.dtor_args;
              DAST._IType _3211___mcc_h127 = _source128.dtor_result;
              {
                RAST._IExpr _out358;
                DCOMP._IOwnership _out359;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out360;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out358, out _out359, out _out360);
                r = _out358;
                resultingOwnership = _out359;
                readIdents = _out360;
              }
            } else if (_source128.is_Primitive) {
              DAST._IPrimitive _3212___mcc_h130 = _source128.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out361;
                DCOMP._IOwnership _out362;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out363;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out361, out _out362, out _out363);
                r = _out361;
                resultingOwnership = _out362;
                readIdents = _out363;
              }
            } else if (_source128.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3213___mcc_h132 = _source128.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out364;
                DCOMP._IOwnership _out365;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out366;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out364, out _out365, out _out366);
                r = _out364;
                resultingOwnership = _out365;
                readIdents = _out366;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3214___mcc_h134 = _source128.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out367;
                DCOMP._IOwnership _out368;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out369;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out367, out _out368, out _out369);
                r = _out367;
                resultingOwnership = _out368;
                readIdents = _out369;
              }
            }
          } else {
            DAST._IType _3215___mcc_h136 = _source125.dtor_baseType;
            DAST._INewtypeRange _3216___mcc_h137 = _source125.dtor_range;
            bool _3217___mcc_h138 = _source125.dtor_erase;
            Dafny.ISequence<DAST._IAttribute> _3218___mcc_h139 = _source125.dtor_attributes;
            DAST._IType _source130 = _3146___mcc_h1;
            if (_source130.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3219___mcc_h152 = _source130.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3220___mcc_h153 = _source130.dtor_typeArgs;
              DAST._IResolvedType _3221___mcc_h154 = _source130.dtor_resolved;
              DAST._IResolvedType _source131 = _3221___mcc_h154;
              if (_source131.is_Datatype) {
                DAST._IDatatypeType _3222___mcc_h161 = _source131.dtor_datatypeType;
                Dafny.ISequence<DAST._IAttribute> _3223_attributes = _3218___mcc_h139;
                bool _3224_erase = _3217___mcc_h138;
                DAST._INewtypeRange _3225_range = _3216___mcc_h137;
                DAST._IType _3226_b = _3215___mcc_h136;
                {
                  RAST._IExpr _out370;
                  DCOMP._IOwnership _out371;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out372;
                  (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out370, out _out371, out _out372);
                  r = _out370;
                  resultingOwnership = _out371;
                  readIdents = _out372;
                }
              } else if (_source131.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3227___mcc_h164 = _source131.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3228___mcc_h165 = _source131.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3229_attributes = _3218___mcc_h139;
                bool _3230_erase = _3217___mcc_h138;
                DAST._INewtypeRange _3231_range = _3216___mcc_h137;
                DAST._IType _3232_b = _3215___mcc_h136;
                {
                  RAST._IExpr _out373;
                  DCOMP._IOwnership _out374;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                  (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out373, out _out374, out _out375);
                  r = _out373;
                  resultingOwnership = _out374;
                  readIdents = _out375;
                }
              } else {
                DAST._IType _3233___mcc_h170 = _source131.dtor_baseType;
                DAST._INewtypeRange _3234___mcc_h171 = _source131.dtor_range;
                bool _3235___mcc_h172 = _source131.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3236___mcc_h173 = _source131.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3237_attributes = _3236___mcc_h173;
                bool _3238_erase = _3235___mcc_h172;
                DAST._INewtypeRange _3239_range = _3234___mcc_h171;
                DAST._IType _3240_b = _3233___mcc_h170;
                {
                  RAST._IExpr _out376;
                  DCOMP._IOwnership _out377;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out378;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out376, out _out377, out _out378);
                  r = _out376;
                  resultingOwnership = _out377;
                  readIdents = _out378;
                }
              }
            } else if (_source130.is_Nullable) {
              DAST._IType _3241___mcc_h182 = _source130.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out379;
                DCOMP._IOwnership _out380;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out381;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out379, out _out380, out _out381);
                r = _out379;
                resultingOwnership = _out380;
                readIdents = _out381;
              }
            } else if (_source130.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3242___mcc_h185 = _source130.dtor_Tuple_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3243_attributes = _3218___mcc_h139;
              bool _3244_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3245_range = _3216___mcc_h137;
              DAST._IType _3246_b = _3215___mcc_h136;
              {
                RAST._IExpr _out382;
                DCOMP._IOwnership _out383;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out384;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out382, out _out383, out _out384);
                r = _out382;
                resultingOwnership = _out383;
                readIdents = _out384;
              }
            } else if (_source130.is_Array) {
              DAST._IType _3247___mcc_h188 = _source130.dtor_element;
              BigInteger _3248___mcc_h189 = _source130.dtor_dims;
              Dafny.ISequence<DAST._IAttribute> _3249_attributes = _3218___mcc_h139;
              bool _3250_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3251_range = _3216___mcc_h137;
              DAST._IType _3252_b = _3215___mcc_h136;
              {
                RAST._IExpr _out385;
                DCOMP._IOwnership _out386;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out385, out _out386, out _out387);
                r = _out385;
                resultingOwnership = _out386;
                readIdents = _out387;
              }
            } else if (_source130.is_Seq) {
              DAST._IType _3253___mcc_h194 = _source130.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3254_attributes = _3218___mcc_h139;
              bool _3255_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3256_range = _3216___mcc_h137;
              DAST._IType _3257_b = _3215___mcc_h136;
              {
                RAST._IExpr _out388;
                DCOMP._IOwnership _out389;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out390;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out388, out _out389, out _out390);
                r = _out388;
                resultingOwnership = _out389;
                readIdents = _out390;
              }
            } else if (_source130.is_Set) {
              DAST._IType _3258___mcc_h197 = _source130.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3259_attributes = _3218___mcc_h139;
              bool _3260_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3261_range = _3216___mcc_h137;
              DAST._IType _3262_b = _3215___mcc_h136;
              {
                RAST._IExpr _out391;
                DCOMP._IOwnership _out392;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out393;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out391, out _out392, out _out393);
                r = _out391;
                resultingOwnership = _out392;
                readIdents = _out393;
              }
            } else if (_source130.is_Multiset) {
              DAST._IType _3263___mcc_h200 = _source130.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3264_attributes = _3218___mcc_h139;
              bool _3265_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3266_range = _3216___mcc_h137;
              DAST._IType _3267_b = _3215___mcc_h136;
              {
                RAST._IExpr _out394;
                DCOMP._IOwnership _out395;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out394, out _out395, out _out396);
                r = _out394;
                resultingOwnership = _out395;
                readIdents = _out396;
              }
            } else if (_source130.is_Map) {
              DAST._IType _3268___mcc_h203 = _source130.dtor_key;
              DAST._IType _3269___mcc_h204 = _source130.dtor_value;
              Dafny.ISequence<DAST._IAttribute> _3270_attributes = _3218___mcc_h139;
              bool _3271_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3272_range = _3216___mcc_h137;
              DAST._IType _3273_b = _3215___mcc_h136;
              {
                RAST._IExpr _out397;
                DCOMP._IOwnership _out398;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out397, out _out398, out _out399);
                r = _out397;
                resultingOwnership = _out398;
                readIdents = _out399;
              }
            } else if (_source130.is_SetBuilder) {
              DAST._IType _3274___mcc_h209 = _source130.dtor_element;
              Dafny.ISequence<DAST._IAttribute> _3275_attributes = _3218___mcc_h139;
              bool _3276_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3277_range = _3216___mcc_h137;
              DAST._IType _3278_b = _3215___mcc_h136;
              {
                RAST._IExpr _out400;
                DCOMP._IOwnership _out401;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out402;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out400, out _out401, out _out402);
                r = _out400;
                resultingOwnership = _out401;
                readIdents = _out402;
              }
            } else if (_source130.is_MapBuilder) {
              DAST._IType _3279___mcc_h212 = _source130.dtor_key;
              DAST._IType _3280___mcc_h213 = _source130.dtor_value;
              Dafny.ISequence<DAST._IAttribute> _3281_attributes = _3218___mcc_h139;
              bool _3282_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3283_range = _3216___mcc_h137;
              DAST._IType _3284_b = _3215___mcc_h136;
              {
                RAST._IExpr _out403;
                DCOMP._IOwnership _out404;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out405;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out403, out _out404, out _out405);
                r = _out403;
                resultingOwnership = _out404;
                readIdents = _out405;
              }
            } else if (_source130.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3285___mcc_h218 = _source130.dtor_args;
              DAST._IType _3286___mcc_h219 = _source130.dtor_result;
              Dafny.ISequence<DAST._IAttribute> _3287_attributes = _3218___mcc_h139;
              bool _3288_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3289_range = _3216___mcc_h137;
              DAST._IType _3290_b = _3215___mcc_h136;
              {
                RAST._IExpr _out406;
                DCOMP._IOwnership _out407;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out408;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out406, out _out407, out _out408);
                r = _out406;
                resultingOwnership = _out407;
                readIdents = _out408;
              }
            } else if (_source130.is_Primitive) {
              DAST._IPrimitive _3291___mcc_h224 = _source130.dtor_Primitive_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3292_attributes = _3218___mcc_h139;
              bool _3293_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3294_range = _3216___mcc_h137;
              DAST._IType _3295_b = _3215___mcc_h136;
              {
                RAST._IExpr _out409;
                DCOMP._IOwnership _out410;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out411;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out409, out _out410, out _out411);
                r = _out409;
                resultingOwnership = _out410;
                readIdents = _out411;
              }
            } else if (_source130.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3296___mcc_h227 = _source130.dtor_Passthrough_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3297_attributes = _3218___mcc_h139;
              bool _3298_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3299_range = _3216___mcc_h137;
              DAST._IType _3300_b = _3215___mcc_h136;
              {
                RAST._IExpr _out412;
                DCOMP._IOwnership _out413;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out412, out _out413, out _out414);
                r = _out412;
                resultingOwnership = _out413;
                readIdents = _out414;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3301___mcc_h230 = _source130.dtor_TypeArg_i_a0;
              Dafny.ISequence<DAST._IAttribute> _3302_attributes = _3218___mcc_h139;
              bool _3303_erase = _3217___mcc_h138;
              DAST._INewtypeRange _3304_range = _3216___mcc_h137;
              DAST._IType _3305_b = _3215___mcc_h136;
              {
                RAST._IExpr _out415;
                DCOMP._IOwnership _out416;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out417;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out415, out _out416, out _out417);
                r = _out415;
                resultingOwnership = _out416;
                readIdents = _out417;
              }
            }
          }
        } else if (_source124.is_Nullable) {
          DAST._IType _3306___mcc_h233 = _source124.dtor_Nullable_i_a0;
          DAST._IType _source132 = _3146___mcc_h1;
          if (_source132.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3307___mcc_h237 = _source132.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3308___mcc_h238 = _source132.dtor_typeArgs;
            DAST._IResolvedType _3309___mcc_h239 = _source132.dtor_resolved;
            DAST._IResolvedType _source133 = _3309___mcc_h239;
            if (_source133.is_Datatype) {
              DAST._IDatatypeType _3310___mcc_h246 = _source133.dtor_datatypeType;
              {
                RAST._IExpr _out418;
                DCOMP._IOwnership _out419;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out420;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out418, out _out419, out _out420);
                r = _out418;
                resultingOwnership = _out419;
                readIdents = _out420;
              }
            } else if (_source133.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3311___mcc_h249 = _source133.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3312___mcc_h250 = _source133.dtor_attributes;
              {
                RAST._IExpr _out421;
                DCOMP._IOwnership _out422;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out421, out _out422, out _out423);
                r = _out421;
                resultingOwnership = _out422;
                readIdents = _out423;
              }
            } else {
              DAST._IType _3313___mcc_h255 = _source133.dtor_baseType;
              DAST._INewtypeRange _3314___mcc_h256 = _source133.dtor_range;
              bool _3315___mcc_h257 = _source133.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3316___mcc_h258 = _source133.dtor_attributes;
              {
                RAST._IExpr _out424;
                DCOMP._IOwnership _out425;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out426;
                (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out424, out _out425, out _out426);
                r = _out424;
                resultingOwnership = _out425;
                readIdents = _out426;
              }
            }
          } else if (_source132.is_Nullable) {
            DAST._IType _3317___mcc_h267 = _source132.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out427, out _out428, out _out429);
              r = _out427;
              resultingOwnership = _out428;
              readIdents = _out429;
            }
          } else if (_source132.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3318___mcc_h270 = _source132.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out430, out _out431, out _out432);
              r = _out430;
              resultingOwnership = _out431;
              readIdents = _out432;
            }
          } else if (_source132.is_Array) {
            DAST._IType _3319___mcc_h273 = _source132.dtor_element;
            BigInteger _3320___mcc_h274 = _source132.dtor_dims;
            {
              RAST._IExpr _out433;
              DCOMP._IOwnership _out434;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out433, out _out434, out _out435);
              r = _out433;
              resultingOwnership = _out434;
              readIdents = _out435;
            }
          } else if (_source132.is_Seq) {
            DAST._IType _3321___mcc_h279 = _source132.dtor_element;
            {
              RAST._IExpr _out436;
              DCOMP._IOwnership _out437;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out438;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out436, out _out437, out _out438);
              r = _out436;
              resultingOwnership = _out437;
              readIdents = _out438;
            }
          } else if (_source132.is_Set) {
            DAST._IType _3322___mcc_h282 = _source132.dtor_element;
            {
              RAST._IExpr _out439;
              DCOMP._IOwnership _out440;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out441;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out439, out _out440, out _out441);
              r = _out439;
              resultingOwnership = _out440;
              readIdents = _out441;
            }
          } else if (_source132.is_Multiset) {
            DAST._IType _3323___mcc_h285 = _source132.dtor_element;
            {
              RAST._IExpr _out442;
              DCOMP._IOwnership _out443;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out442, out _out443, out _out444);
              r = _out442;
              resultingOwnership = _out443;
              readIdents = _out444;
            }
          } else if (_source132.is_Map) {
            DAST._IType _3324___mcc_h288 = _source132.dtor_key;
            DAST._IType _3325___mcc_h289 = _source132.dtor_value;
            {
              RAST._IExpr _out445;
              DCOMP._IOwnership _out446;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out445, out _out446, out _out447);
              r = _out445;
              resultingOwnership = _out446;
              readIdents = _out447;
            }
          } else if (_source132.is_SetBuilder) {
            DAST._IType _3326___mcc_h294 = _source132.dtor_element;
            {
              RAST._IExpr _out448;
              DCOMP._IOwnership _out449;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out448, out _out449, out _out450);
              r = _out448;
              resultingOwnership = _out449;
              readIdents = _out450;
            }
          } else if (_source132.is_MapBuilder) {
            DAST._IType _3327___mcc_h297 = _source132.dtor_key;
            DAST._IType _3328___mcc_h298 = _source132.dtor_value;
            {
              RAST._IExpr _out451;
              DCOMP._IOwnership _out452;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out453;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out451, out _out452, out _out453);
              r = _out451;
              resultingOwnership = _out452;
              readIdents = _out453;
            }
          } else if (_source132.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3329___mcc_h303 = _source132.dtor_args;
            DAST._IType _3330___mcc_h304 = _source132.dtor_result;
            {
              RAST._IExpr _out454;
              DCOMP._IOwnership _out455;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out454, out _out455, out _out456);
              r = _out454;
              resultingOwnership = _out455;
              readIdents = _out456;
            }
          } else if (_source132.is_Primitive) {
            DAST._IPrimitive _3331___mcc_h309 = _source132.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out457;
              DCOMP._IOwnership _out458;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out457, out _out458, out _out459);
              r = _out457;
              resultingOwnership = _out458;
              readIdents = _out459;
            }
          } else if (_source132.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3332___mcc_h312 = _source132.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out460;
              DCOMP._IOwnership _out461;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out462;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out460, out _out461, out _out462);
              r = _out460;
              resultingOwnership = _out461;
              readIdents = _out462;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3333___mcc_h315 = _source132.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out463;
              DCOMP._IOwnership _out464;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out465;
              (this).GenExprConvertFromNullable(e, selfIdent, env, expectedOwnership, out _out463, out _out464, out _out465);
              r = _out463;
              resultingOwnership = _out464;
              readIdents = _out465;
            }
          }
        } else if (_source124.is_Tuple) {
          Dafny.ISequence<DAST._IType> _3334___mcc_h318 = _source124.dtor_Tuple_i_a0;
          DAST._IType _source134 = _3146___mcc_h1;
          if (_source134.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3335___mcc_h322 = _source134.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3336___mcc_h323 = _source134.dtor_typeArgs;
            DAST._IResolvedType _3337___mcc_h324 = _source134.dtor_resolved;
            DAST._IResolvedType _source135 = _3337___mcc_h324;
            if (_source135.is_Datatype) {
              DAST._IDatatypeType _3338___mcc_h328 = _source135.dtor_datatypeType;
              {
                RAST._IExpr _out466;
                DCOMP._IOwnership _out467;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out466, out _out467, out _out468);
                r = _out466;
                resultingOwnership = _out467;
                readIdents = _out468;
              }
            } else if (_source135.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3339___mcc_h330 = _source135.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3340___mcc_h331 = _source135.dtor_attributes;
              {
                RAST._IExpr _out469;
                DCOMP._IOwnership _out470;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out469, out _out470, out _out471);
                r = _out469;
                resultingOwnership = _out470;
                readIdents = _out471;
              }
            } else {
              DAST._IType _3341___mcc_h334 = _source135.dtor_baseType;
              DAST._INewtypeRange _3342___mcc_h335 = _source135.dtor_range;
              bool _3343___mcc_h336 = _source135.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3344___mcc_h337 = _source135.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3345_attributes = _3344___mcc_h337;
              bool _3346_erase = _3343___mcc_h336;
              DAST._INewtypeRange _3347_range = _3342___mcc_h335;
              DAST._IType _3348_b = _3341___mcc_h334;
              {
                RAST._IExpr _out472;
                DCOMP._IOwnership _out473;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out472, out _out473, out _out474);
                r = _out472;
                resultingOwnership = _out473;
                readIdents = _out474;
              }
            }
          } else if (_source134.is_Nullable) {
            DAST._IType _3349___mcc_h342 = _source134.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out475;
              DCOMP._IOwnership _out476;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out477;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out475, out _out476, out _out477);
              r = _out475;
              resultingOwnership = _out476;
              readIdents = _out477;
            }
          } else if (_source134.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3350___mcc_h344 = _source134.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out478;
              DCOMP._IOwnership _out479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out478, out _out479, out _out480);
              r = _out478;
              resultingOwnership = _out479;
              readIdents = _out480;
            }
          } else if (_source134.is_Array) {
            DAST._IType _3351___mcc_h346 = _source134.dtor_element;
            BigInteger _3352___mcc_h347 = _source134.dtor_dims;
            {
              RAST._IExpr _out481;
              DCOMP._IOwnership _out482;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out483;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out481, out _out482, out _out483);
              r = _out481;
              resultingOwnership = _out482;
              readIdents = _out483;
            }
          } else if (_source134.is_Seq) {
            DAST._IType _3353___mcc_h350 = _source134.dtor_element;
            {
              RAST._IExpr _out484;
              DCOMP._IOwnership _out485;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out486;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out484, out _out485, out _out486);
              r = _out484;
              resultingOwnership = _out485;
              readIdents = _out486;
            }
          } else if (_source134.is_Set) {
            DAST._IType _3354___mcc_h352 = _source134.dtor_element;
            {
              RAST._IExpr _out487;
              DCOMP._IOwnership _out488;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out489;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out487, out _out488, out _out489);
              r = _out487;
              resultingOwnership = _out488;
              readIdents = _out489;
            }
          } else if (_source134.is_Multiset) {
            DAST._IType _3355___mcc_h354 = _source134.dtor_element;
            {
              RAST._IExpr _out490;
              DCOMP._IOwnership _out491;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out490, out _out491, out _out492);
              r = _out490;
              resultingOwnership = _out491;
              readIdents = _out492;
            }
          } else if (_source134.is_Map) {
            DAST._IType _3356___mcc_h356 = _source134.dtor_key;
            DAST._IType _3357___mcc_h357 = _source134.dtor_value;
            {
              RAST._IExpr _out493;
              DCOMP._IOwnership _out494;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out495;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out493, out _out494, out _out495);
              r = _out493;
              resultingOwnership = _out494;
              readIdents = _out495;
            }
          } else if (_source134.is_SetBuilder) {
            DAST._IType _3358___mcc_h360 = _source134.dtor_element;
            {
              RAST._IExpr _out496;
              DCOMP._IOwnership _out497;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out498;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out496, out _out497, out _out498);
              r = _out496;
              resultingOwnership = _out497;
              readIdents = _out498;
            }
          } else if (_source134.is_MapBuilder) {
            DAST._IType _3359___mcc_h362 = _source134.dtor_key;
            DAST._IType _3360___mcc_h363 = _source134.dtor_value;
            {
              RAST._IExpr _out499;
              DCOMP._IOwnership _out500;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out501;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out499, out _out500, out _out501);
              r = _out499;
              resultingOwnership = _out500;
              readIdents = _out501;
            }
          } else if (_source134.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3361___mcc_h366 = _source134.dtor_args;
            DAST._IType _3362___mcc_h367 = _source134.dtor_result;
            {
              RAST._IExpr _out502;
              DCOMP._IOwnership _out503;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out502, out _out503, out _out504);
              r = _out502;
              resultingOwnership = _out503;
              readIdents = _out504;
            }
          } else if (_source134.is_Primitive) {
            DAST._IPrimitive _3363___mcc_h370 = _source134.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out505;
              DCOMP._IOwnership _out506;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out507;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out505, out _out506, out _out507);
              r = _out505;
              resultingOwnership = _out506;
              readIdents = _out507;
            }
          } else if (_source134.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3364___mcc_h372 = _source134.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out508;
              DCOMP._IOwnership _out509;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out510;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out508, out _out509, out _out510);
              r = _out508;
              resultingOwnership = _out509;
              readIdents = _out510;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3365___mcc_h374 = _source134.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out511;
              DCOMP._IOwnership _out512;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out513;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out511, out _out512, out _out513);
              r = _out511;
              resultingOwnership = _out512;
              readIdents = _out513;
            }
          }
        } else if (_source124.is_Array) {
          DAST._IType _3366___mcc_h376 = _source124.dtor_element;
          BigInteger _3367___mcc_h377 = _source124.dtor_dims;
          DAST._IType _source136 = _3146___mcc_h1;
          if (_source136.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3368___mcc_h384 = _source136.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3369___mcc_h385 = _source136.dtor_typeArgs;
            DAST._IResolvedType _3370___mcc_h386 = _source136.dtor_resolved;
            DAST._IResolvedType _source137 = _3370___mcc_h386;
            if (_source137.is_Datatype) {
              DAST._IDatatypeType _3371___mcc_h390 = _source137.dtor_datatypeType;
              {
                RAST._IExpr _out514;
                DCOMP._IOwnership _out515;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out514, out _out515, out _out516);
                r = _out514;
                resultingOwnership = _out515;
                readIdents = _out516;
              }
            } else if (_source137.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3372___mcc_h392 = _source137.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3373___mcc_h393 = _source137.dtor_attributes;
              {
                RAST._IExpr _out517;
                DCOMP._IOwnership _out518;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out517, out _out518, out _out519);
                r = _out517;
                resultingOwnership = _out518;
                readIdents = _out519;
              }
            } else {
              DAST._IType _3374___mcc_h396 = _source137.dtor_baseType;
              DAST._INewtypeRange _3375___mcc_h397 = _source137.dtor_range;
              bool _3376___mcc_h398 = _source137.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3377___mcc_h399 = _source137.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3378_attributes = _3377___mcc_h399;
              bool _3379_erase = _3376___mcc_h398;
              DAST._INewtypeRange _3380_range = _3375___mcc_h397;
              DAST._IType _3381_b = _3374___mcc_h396;
              {
                RAST._IExpr _out520;
                DCOMP._IOwnership _out521;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out522;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out520, out _out521, out _out522);
                r = _out520;
                resultingOwnership = _out521;
                readIdents = _out522;
              }
            }
          } else if (_source136.is_Nullable) {
            DAST._IType _3382___mcc_h404 = _source136.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out523;
              DCOMP._IOwnership _out524;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out523, out _out524, out _out525);
              r = _out523;
              resultingOwnership = _out524;
              readIdents = _out525;
            }
          } else if (_source136.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3383___mcc_h406 = _source136.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out526;
              DCOMP._IOwnership _out527;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out528;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out526, out _out527, out _out528);
              r = _out526;
              resultingOwnership = _out527;
              readIdents = _out528;
            }
          } else if (_source136.is_Array) {
            DAST._IType _3384___mcc_h408 = _source136.dtor_element;
            BigInteger _3385___mcc_h409 = _source136.dtor_dims;
            {
              RAST._IExpr _out529;
              DCOMP._IOwnership _out530;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out531;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out529, out _out530, out _out531);
              r = _out529;
              resultingOwnership = _out530;
              readIdents = _out531;
            }
          } else if (_source136.is_Seq) {
            DAST._IType _3386___mcc_h412 = _source136.dtor_element;
            {
              RAST._IExpr _out532;
              DCOMP._IOwnership _out533;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out534;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out532, out _out533, out _out534);
              r = _out532;
              resultingOwnership = _out533;
              readIdents = _out534;
            }
          } else if (_source136.is_Set) {
            DAST._IType _3387___mcc_h414 = _source136.dtor_element;
            {
              RAST._IExpr _out535;
              DCOMP._IOwnership _out536;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out537;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out535, out _out536, out _out537);
              r = _out535;
              resultingOwnership = _out536;
              readIdents = _out537;
            }
          } else if (_source136.is_Multiset) {
            DAST._IType _3388___mcc_h416 = _source136.dtor_element;
            {
              RAST._IExpr _out538;
              DCOMP._IOwnership _out539;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out540;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out538, out _out539, out _out540);
              r = _out538;
              resultingOwnership = _out539;
              readIdents = _out540;
            }
          } else if (_source136.is_Map) {
            DAST._IType _3389___mcc_h418 = _source136.dtor_key;
            DAST._IType _3390___mcc_h419 = _source136.dtor_value;
            {
              RAST._IExpr _out541;
              DCOMP._IOwnership _out542;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out543;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out541, out _out542, out _out543);
              r = _out541;
              resultingOwnership = _out542;
              readIdents = _out543;
            }
          } else if (_source136.is_SetBuilder) {
            DAST._IType _3391___mcc_h422 = _source136.dtor_element;
            {
              RAST._IExpr _out544;
              DCOMP._IOwnership _out545;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out544, out _out545, out _out546);
              r = _out544;
              resultingOwnership = _out545;
              readIdents = _out546;
            }
          } else if (_source136.is_MapBuilder) {
            DAST._IType _3392___mcc_h424 = _source136.dtor_key;
            DAST._IType _3393___mcc_h425 = _source136.dtor_value;
            {
              RAST._IExpr _out547;
              DCOMP._IOwnership _out548;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out547, out _out548, out _out549);
              r = _out547;
              resultingOwnership = _out548;
              readIdents = _out549;
            }
          } else if (_source136.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3394___mcc_h428 = _source136.dtor_args;
            DAST._IType _3395___mcc_h429 = _source136.dtor_result;
            {
              RAST._IExpr _out550;
              DCOMP._IOwnership _out551;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out550, out _out551, out _out552);
              r = _out550;
              resultingOwnership = _out551;
              readIdents = _out552;
            }
          } else if (_source136.is_Primitive) {
            DAST._IPrimitive _3396___mcc_h432 = _source136.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out553;
              DCOMP._IOwnership _out554;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out555;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out553, out _out554, out _out555);
              r = _out553;
              resultingOwnership = _out554;
              readIdents = _out555;
            }
          } else if (_source136.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3397___mcc_h434 = _source136.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out556;
              DCOMP._IOwnership _out557;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out558;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out556, out _out557, out _out558);
              r = _out556;
              resultingOwnership = _out557;
              readIdents = _out558;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3398___mcc_h436 = _source136.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out559;
              DCOMP._IOwnership _out560;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out561;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out559, out _out560, out _out561);
              r = _out559;
              resultingOwnership = _out560;
              readIdents = _out561;
            }
          }
        } else if (_source124.is_Seq) {
          DAST._IType _3399___mcc_h438 = _source124.dtor_element;
          DAST._IType _source138 = _3146___mcc_h1;
          if (_source138.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3400___mcc_h442 = _source138.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3401___mcc_h443 = _source138.dtor_typeArgs;
            DAST._IResolvedType _3402___mcc_h444 = _source138.dtor_resolved;
            DAST._IResolvedType _source139 = _3402___mcc_h444;
            if (_source139.is_Datatype) {
              DAST._IDatatypeType _3403___mcc_h448 = _source139.dtor_datatypeType;
              {
                RAST._IExpr _out562;
                DCOMP._IOwnership _out563;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out564;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out562, out _out563, out _out564);
                r = _out562;
                resultingOwnership = _out563;
                readIdents = _out564;
              }
            } else if (_source139.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3404___mcc_h450 = _source139.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3405___mcc_h451 = _source139.dtor_attributes;
              {
                RAST._IExpr _out565;
                DCOMP._IOwnership _out566;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out567;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out565, out _out566, out _out567);
                r = _out565;
                resultingOwnership = _out566;
                readIdents = _out567;
              }
            } else {
              DAST._IType _3406___mcc_h454 = _source139.dtor_baseType;
              DAST._INewtypeRange _3407___mcc_h455 = _source139.dtor_range;
              bool _3408___mcc_h456 = _source139.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3409___mcc_h457 = _source139.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3410_attributes = _3409___mcc_h457;
              bool _3411_erase = _3408___mcc_h456;
              DAST._INewtypeRange _3412_range = _3407___mcc_h455;
              DAST._IType _3413_b = _3406___mcc_h454;
              {
                RAST._IExpr _out568;
                DCOMP._IOwnership _out569;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out570;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out568, out _out569, out _out570);
                r = _out568;
                resultingOwnership = _out569;
                readIdents = _out570;
              }
            }
          } else if (_source138.is_Nullable) {
            DAST._IType _3414___mcc_h462 = _source138.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out571;
              DCOMP._IOwnership _out572;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out573;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out571, out _out572, out _out573);
              r = _out571;
              resultingOwnership = _out572;
              readIdents = _out573;
            }
          } else if (_source138.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3415___mcc_h464 = _source138.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out574;
              DCOMP._IOwnership _out575;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out576;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out574, out _out575, out _out576);
              r = _out574;
              resultingOwnership = _out575;
              readIdents = _out576;
            }
          } else if (_source138.is_Array) {
            DAST._IType _3416___mcc_h466 = _source138.dtor_element;
            BigInteger _3417___mcc_h467 = _source138.dtor_dims;
            {
              RAST._IExpr _out577;
              DCOMP._IOwnership _out578;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out579;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out577, out _out578, out _out579);
              r = _out577;
              resultingOwnership = _out578;
              readIdents = _out579;
            }
          } else if (_source138.is_Seq) {
            DAST._IType _3418___mcc_h470 = _source138.dtor_element;
            {
              RAST._IExpr _out580;
              DCOMP._IOwnership _out581;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out580, out _out581, out _out582);
              r = _out580;
              resultingOwnership = _out581;
              readIdents = _out582;
            }
          } else if (_source138.is_Set) {
            DAST._IType _3419___mcc_h472 = _source138.dtor_element;
            {
              RAST._IExpr _out583;
              DCOMP._IOwnership _out584;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out585;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out583, out _out584, out _out585);
              r = _out583;
              resultingOwnership = _out584;
              readIdents = _out585;
            }
          } else if (_source138.is_Multiset) {
            DAST._IType _3420___mcc_h474 = _source138.dtor_element;
            {
              RAST._IExpr _out586;
              DCOMP._IOwnership _out587;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out588;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out586, out _out587, out _out588);
              r = _out586;
              resultingOwnership = _out587;
              readIdents = _out588;
            }
          } else if (_source138.is_Map) {
            DAST._IType _3421___mcc_h476 = _source138.dtor_key;
            DAST._IType _3422___mcc_h477 = _source138.dtor_value;
            {
              RAST._IExpr _out589;
              DCOMP._IOwnership _out590;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out591;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out589, out _out590, out _out591);
              r = _out589;
              resultingOwnership = _out590;
              readIdents = _out591;
            }
          } else if (_source138.is_SetBuilder) {
            DAST._IType _3423___mcc_h480 = _source138.dtor_element;
            {
              RAST._IExpr _out592;
              DCOMP._IOwnership _out593;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out592, out _out593, out _out594);
              r = _out592;
              resultingOwnership = _out593;
              readIdents = _out594;
            }
          } else if (_source138.is_MapBuilder) {
            DAST._IType _3424___mcc_h482 = _source138.dtor_key;
            DAST._IType _3425___mcc_h483 = _source138.dtor_value;
            {
              RAST._IExpr _out595;
              DCOMP._IOwnership _out596;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out595, out _out596, out _out597);
              r = _out595;
              resultingOwnership = _out596;
              readIdents = _out597;
            }
          } else if (_source138.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3426___mcc_h486 = _source138.dtor_args;
            DAST._IType _3427___mcc_h487 = _source138.dtor_result;
            {
              RAST._IExpr _out598;
              DCOMP._IOwnership _out599;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out600;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out598, out _out599, out _out600);
              r = _out598;
              resultingOwnership = _out599;
              readIdents = _out600;
            }
          } else if (_source138.is_Primitive) {
            DAST._IPrimitive _3428___mcc_h490 = _source138.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out601;
              DCOMP._IOwnership _out602;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out603;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out601, out _out602, out _out603);
              r = _out601;
              resultingOwnership = _out602;
              readIdents = _out603;
            }
          } else if (_source138.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3429___mcc_h492 = _source138.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out604;
              DCOMP._IOwnership _out605;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out604, out _out605, out _out606);
              r = _out604;
              resultingOwnership = _out605;
              readIdents = _out606;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3430___mcc_h494 = _source138.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out607;
              DCOMP._IOwnership _out608;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out609;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out607, out _out608, out _out609);
              r = _out607;
              resultingOwnership = _out608;
              readIdents = _out609;
            }
          }
        } else if (_source124.is_Set) {
          DAST._IType _3431___mcc_h496 = _source124.dtor_element;
          DAST._IType _source140 = _3146___mcc_h1;
          if (_source140.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3432___mcc_h500 = _source140.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3433___mcc_h501 = _source140.dtor_typeArgs;
            DAST._IResolvedType _3434___mcc_h502 = _source140.dtor_resolved;
            DAST._IResolvedType _source141 = _3434___mcc_h502;
            if (_source141.is_Datatype) {
              DAST._IDatatypeType _3435___mcc_h506 = _source141.dtor_datatypeType;
              {
                RAST._IExpr _out610;
                DCOMP._IOwnership _out611;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out612;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out610, out _out611, out _out612);
                r = _out610;
                resultingOwnership = _out611;
                readIdents = _out612;
              }
            } else if (_source141.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3436___mcc_h508 = _source141.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3437___mcc_h509 = _source141.dtor_attributes;
              {
                RAST._IExpr _out613;
                DCOMP._IOwnership _out614;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out615;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out613, out _out614, out _out615);
                r = _out613;
                resultingOwnership = _out614;
                readIdents = _out615;
              }
            } else {
              DAST._IType _3438___mcc_h512 = _source141.dtor_baseType;
              DAST._INewtypeRange _3439___mcc_h513 = _source141.dtor_range;
              bool _3440___mcc_h514 = _source141.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3441___mcc_h515 = _source141.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3442_attributes = _3441___mcc_h515;
              bool _3443_erase = _3440___mcc_h514;
              DAST._INewtypeRange _3444_range = _3439___mcc_h513;
              DAST._IType _3445_b = _3438___mcc_h512;
              {
                RAST._IExpr _out616;
                DCOMP._IOwnership _out617;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out618;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out616, out _out617, out _out618);
                r = _out616;
                resultingOwnership = _out617;
                readIdents = _out618;
              }
            }
          } else if (_source140.is_Nullable) {
            DAST._IType _3446___mcc_h520 = _source140.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out619;
              DCOMP._IOwnership _out620;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out621;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out619, out _out620, out _out621);
              r = _out619;
              resultingOwnership = _out620;
              readIdents = _out621;
            }
          } else if (_source140.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3447___mcc_h522 = _source140.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out622;
              DCOMP._IOwnership _out623;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out624;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out622, out _out623, out _out624);
              r = _out622;
              resultingOwnership = _out623;
              readIdents = _out624;
            }
          } else if (_source140.is_Array) {
            DAST._IType _3448___mcc_h524 = _source140.dtor_element;
            BigInteger _3449___mcc_h525 = _source140.dtor_dims;
            {
              RAST._IExpr _out625;
              DCOMP._IOwnership _out626;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out625, out _out626, out _out627);
              r = _out625;
              resultingOwnership = _out626;
              readIdents = _out627;
            }
          } else if (_source140.is_Seq) {
            DAST._IType _3450___mcc_h528 = _source140.dtor_element;
            {
              RAST._IExpr _out628;
              DCOMP._IOwnership _out629;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out628, out _out629, out _out630);
              r = _out628;
              resultingOwnership = _out629;
              readIdents = _out630;
            }
          } else if (_source140.is_Set) {
            DAST._IType _3451___mcc_h530 = _source140.dtor_element;
            {
              RAST._IExpr _out631;
              DCOMP._IOwnership _out632;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out633;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out631, out _out632, out _out633);
              r = _out631;
              resultingOwnership = _out632;
              readIdents = _out633;
            }
          } else if (_source140.is_Multiset) {
            DAST._IType _3452___mcc_h532 = _source140.dtor_element;
            {
              RAST._IExpr _out634;
              DCOMP._IOwnership _out635;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out636;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out634, out _out635, out _out636);
              r = _out634;
              resultingOwnership = _out635;
              readIdents = _out636;
            }
          } else if (_source140.is_Map) {
            DAST._IType _3453___mcc_h534 = _source140.dtor_key;
            DAST._IType _3454___mcc_h535 = _source140.dtor_value;
            {
              RAST._IExpr _out637;
              DCOMP._IOwnership _out638;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out639;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out637, out _out638, out _out639);
              r = _out637;
              resultingOwnership = _out638;
              readIdents = _out639;
            }
          } else if (_source140.is_SetBuilder) {
            DAST._IType _3455___mcc_h538 = _source140.dtor_element;
            {
              RAST._IExpr _out640;
              DCOMP._IOwnership _out641;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out642;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out640, out _out641, out _out642);
              r = _out640;
              resultingOwnership = _out641;
              readIdents = _out642;
            }
          } else if (_source140.is_MapBuilder) {
            DAST._IType _3456___mcc_h540 = _source140.dtor_key;
            DAST._IType _3457___mcc_h541 = _source140.dtor_value;
            {
              RAST._IExpr _out643;
              DCOMP._IOwnership _out644;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out643, out _out644, out _out645);
              r = _out643;
              resultingOwnership = _out644;
              readIdents = _out645;
            }
          } else if (_source140.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3458___mcc_h544 = _source140.dtor_args;
            DAST._IType _3459___mcc_h545 = _source140.dtor_result;
            {
              RAST._IExpr _out646;
              DCOMP._IOwnership _out647;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out648;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out646, out _out647, out _out648);
              r = _out646;
              resultingOwnership = _out647;
              readIdents = _out648;
            }
          } else if (_source140.is_Primitive) {
            DAST._IPrimitive _3460___mcc_h548 = _source140.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out649;
              DCOMP._IOwnership _out650;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out651;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out649, out _out650, out _out651);
              r = _out649;
              resultingOwnership = _out650;
              readIdents = _out651;
            }
          } else if (_source140.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3461___mcc_h550 = _source140.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out652;
              DCOMP._IOwnership _out653;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out654;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out652, out _out653, out _out654);
              r = _out652;
              resultingOwnership = _out653;
              readIdents = _out654;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3462___mcc_h552 = _source140.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out655;
              DCOMP._IOwnership _out656;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out657;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out655, out _out656, out _out657);
              r = _out655;
              resultingOwnership = _out656;
              readIdents = _out657;
            }
          }
        } else if (_source124.is_Multiset) {
          DAST._IType _3463___mcc_h554 = _source124.dtor_element;
          DAST._IType _source142 = _3146___mcc_h1;
          if (_source142.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3464___mcc_h558 = _source142.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3465___mcc_h559 = _source142.dtor_typeArgs;
            DAST._IResolvedType _3466___mcc_h560 = _source142.dtor_resolved;
            DAST._IResolvedType _source143 = _3466___mcc_h560;
            if (_source143.is_Datatype) {
              DAST._IDatatypeType _3467___mcc_h564 = _source143.dtor_datatypeType;
              {
                RAST._IExpr _out658;
                DCOMP._IOwnership _out659;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out658, out _out659, out _out660);
                r = _out658;
                resultingOwnership = _out659;
                readIdents = _out660;
              }
            } else if (_source143.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3468___mcc_h566 = _source143.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3469___mcc_h567 = _source143.dtor_attributes;
              {
                RAST._IExpr _out661;
                DCOMP._IOwnership _out662;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out661, out _out662, out _out663);
                r = _out661;
                resultingOwnership = _out662;
                readIdents = _out663;
              }
            } else {
              DAST._IType _3470___mcc_h570 = _source143.dtor_baseType;
              DAST._INewtypeRange _3471___mcc_h571 = _source143.dtor_range;
              bool _3472___mcc_h572 = _source143.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3473___mcc_h573 = _source143.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3474_attributes = _3473___mcc_h573;
              bool _3475_erase = _3472___mcc_h572;
              DAST._INewtypeRange _3476_range = _3471___mcc_h571;
              DAST._IType _3477_b = _3470___mcc_h570;
              {
                RAST._IExpr _out664;
                DCOMP._IOwnership _out665;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out666;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out664, out _out665, out _out666);
                r = _out664;
                resultingOwnership = _out665;
                readIdents = _out666;
              }
            }
          } else if (_source142.is_Nullable) {
            DAST._IType _3478___mcc_h578 = _source142.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out667;
              DCOMP._IOwnership _out668;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out669;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out667, out _out668, out _out669);
              r = _out667;
              resultingOwnership = _out668;
              readIdents = _out669;
            }
          } else if (_source142.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3479___mcc_h580 = _source142.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out670;
              DCOMP._IOwnership _out671;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out672;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out670, out _out671, out _out672);
              r = _out670;
              resultingOwnership = _out671;
              readIdents = _out672;
            }
          } else if (_source142.is_Array) {
            DAST._IType _3480___mcc_h582 = _source142.dtor_element;
            BigInteger _3481___mcc_h583 = _source142.dtor_dims;
            {
              RAST._IExpr _out673;
              DCOMP._IOwnership _out674;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out675;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out673, out _out674, out _out675);
              r = _out673;
              resultingOwnership = _out674;
              readIdents = _out675;
            }
          } else if (_source142.is_Seq) {
            DAST._IType _3482___mcc_h586 = _source142.dtor_element;
            {
              RAST._IExpr _out676;
              DCOMP._IOwnership _out677;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out678;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out676, out _out677, out _out678);
              r = _out676;
              resultingOwnership = _out677;
              readIdents = _out678;
            }
          } else if (_source142.is_Set) {
            DAST._IType _3483___mcc_h588 = _source142.dtor_element;
            {
              RAST._IExpr _out679;
              DCOMP._IOwnership _out680;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out681;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out679, out _out680, out _out681);
              r = _out679;
              resultingOwnership = _out680;
              readIdents = _out681;
            }
          } else if (_source142.is_Multiset) {
            DAST._IType _3484___mcc_h590 = _source142.dtor_element;
            {
              RAST._IExpr _out682;
              DCOMP._IOwnership _out683;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out684;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out682, out _out683, out _out684);
              r = _out682;
              resultingOwnership = _out683;
              readIdents = _out684;
            }
          } else if (_source142.is_Map) {
            DAST._IType _3485___mcc_h592 = _source142.dtor_key;
            DAST._IType _3486___mcc_h593 = _source142.dtor_value;
            {
              RAST._IExpr _out685;
              DCOMP._IOwnership _out686;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out687;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out685, out _out686, out _out687);
              r = _out685;
              resultingOwnership = _out686;
              readIdents = _out687;
            }
          } else if (_source142.is_SetBuilder) {
            DAST._IType _3487___mcc_h596 = _source142.dtor_element;
            {
              RAST._IExpr _out688;
              DCOMP._IOwnership _out689;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out690;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out688, out _out689, out _out690);
              r = _out688;
              resultingOwnership = _out689;
              readIdents = _out690;
            }
          } else if (_source142.is_MapBuilder) {
            DAST._IType _3488___mcc_h598 = _source142.dtor_key;
            DAST._IType _3489___mcc_h599 = _source142.dtor_value;
            {
              RAST._IExpr _out691;
              DCOMP._IOwnership _out692;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out693;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out691, out _out692, out _out693);
              r = _out691;
              resultingOwnership = _out692;
              readIdents = _out693;
            }
          } else if (_source142.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3490___mcc_h602 = _source142.dtor_args;
            DAST._IType _3491___mcc_h603 = _source142.dtor_result;
            {
              RAST._IExpr _out694;
              DCOMP._IOwnership _out695;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out696;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out694, out _out695, out _out696);
              r = _out694;
              resultingOwnership = _out695;
              readIdents = _out696;
            }
          } else if (_source142.is_Primitive) {
            DAST._IPrimitive _3492___mcc_h606 = _source142.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out697;
              DCOMP._IOwnership _out698;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out699;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out697, out _out698, out _out699);
              r = _out697;
              resultingOwnership = _out698;
              readIdents = _out699;
            }
          } else if (_source142.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3493___mcc_h608 = _source142.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out700;
              DCOMP._IOwnership _out701;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out702;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out700, out _out701, out _out702);
              r = _out700;
              resultingOwnership = _out701;
              readIdents = _out702;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3494___mcc_h610 = _source142.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out703;
              DCOMP._IOwnership _out704;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out705;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out703, out _out704, out _out705);
              r = _out703;
              resultingOwnership = _out704;
              readIdents = _out705;
            }
          }
        } else if (_source124.is_Map) {
          DAST._IType _3495___mcc_h612 = _source124.dtor_key;
          DAST._IType _3496___mcc_h613 = _source124.dtor_value;
          DAST._IType _source144 = _3146___mcc_h1;
          if (_source144.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3497___mcc_h620 = _source144.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3498___mcc_h621 = _source144.dtor_typeArgs;
            DAST._IResolvedType _3499___mcc_h622 = _source144.dtor_resolved;
            DAST._IResolvedType _source145 = _3499___mcc_h622;
            if (_source145.is_Datatype) {
              DAST._IDatatypeType _3500___mcc_h626 = _source145.dtor_datatypeType;
              {
                RAST._IExpr _out706;
                DCOMP._IOwnership _out707;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out708;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out706, out _out707, out _out708);
                r = _out706;
                resultingOwnership = _out707;
                readIdents = _out708;
              }
            } else if (_source145.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3501___mcc_h628 = _source145.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3502___mcc_h629 = _source145.dtor_attributes;
              {
                RAST._IExpr _out709;
                DCOMP._IOwnership _out710;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out711;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out709, out _out710, out _out711);
                r = _out709;
                resultingOwnership = _out710;
                readIdents = _out711;
              }
            } else {
              DAST._IType _3503___mcc_h632 = _source145.dtor_baseType;
              DAST._INewtypeRange _3504___mcc_h633 = _source145.dtor_range;
              bool _3505___mcc_h634 = _source145.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3506___mcc_h635 = _source145.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3507_attributes = _3506___mcc_h635;
              bool _3508_erase = _3505___mcc_h634;
              DAST._INewtypeRange _3509_range = _3504___mcc_h633;
              DAST._IType _3510_b = _3503___mcc_h632;
              {
                RAST._IExpr _out712;
                DCOMP._IOwnership _out713;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out714;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out712, out _out713, out _out714);
                r = _out712;
                resultingOwnership = _out713;
                readIdents = _out714;
              }
            }
          } else if (_source144.is_Nullable) {
            DAST._IType _3511___mcc_h640 = _source144.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out715;
              DCOMP._IOwnership _out716;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out717;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out715, out _out716, out _out717);
              r = _out715;
              resultingOwnership = _out716;
              readIdents = _out717;
            }
          } else if (_source144.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3512___mcc_h642 = _source144.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out718;
              DCOMP._IOwnership _out719;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out720;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out718, out _out719, out _out720);
              r = _out718;
              resultingOwnership = _out719;
              readIdents = _out720;
            }
          } else if (_source144.is_Array) {
            DAST._IType _3513___mcc_h644 = _source144.dtor_element;
            BigInteger _3514___mcc_h645 = _source144.dtor_dims;
            {
              RAST._IExpr _out721;
              DCOMP._IOwnership _out722;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out723;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out721, out _out722, out _out723);
              r = _out721;
              resultingOwnership = _out722;
              readIdents = _out723;
            }
          } else if (_source144.is_Seq) {
            DAST._IType _3515___mcc_h648 = _source144.dtor_element;
            {
              RAST._IExpr _out724;
              DCOMP._IOwnership _out725;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out726;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out724, out _out725, out _out726);
              r = _out724;
              resultingOwnership = _out725;
              readIdents = _out726;
            }
          } else if (_source144.is_Set) {
            DAST._IType _3516___mcc_h650 = _source144.dtor_element;
            {
              RAST._IExpr _out727;
              DCOMP._IOwnership _out728;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out729;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out727, out _out728, out _out729);
              r = _out727;
              resultingOwnership = _out728;
              readIdents = _out729;
            }
          } else if (_source144.is_Multiset) {
            DAST._IType _3517___mcc_h652 = _source144.dtor_element;
            {
              RAST._IExpr _out730;
              DCOMP._IOwnership _out731;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out732;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out730, out _out731, out _out732);
              r = _out730;
              resultingOwnership = _out731;
              readIdents = _out732;
            }
          } else if (_source144.is_Map) {
            DAST._IType _3518___mcc_h654 = _source144.dtor_key;
            DAST._IType _3519___mcc_h655 = _source144.dtor_value;
            {
              RAST._IExpr _out733;
              DCOMP._IOwnership _out734;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out735;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out733, out _out734, out _out735);
              r = _out733;
              resultingOwnership = _out734;
              readIdents = _out735;
            }
          } else if (_source144.is_SetBuilder) {
            DAST._IType _3520___mcc_h658 = _source144.dtor_element;
            {
              RAST._IExpr _out736;
              DCOMP._IOwnership _out737;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out738;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out736, out _out737, out _out738);
              r = _out736;
              resultingOwnership = _out737;
              readIdents = _out738;
            }
          } else if (_source144.is_MapBuilder) {
            DAST._IType _3521___mcc_h660 = _source144.dtor_key;
            DAST._IType _3522___mcc_h661 = _source144.dtor_value;
            {
              RAST._IExpr _out739;
              DCOMP._IOwnership _out740;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out741;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out739, out _out740, out _out741);
              r = _out739;
              resultingOwnership = _out740;
              readIdents = _out741;
            }
          } else if (_source144.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3523___mcc_h664 = _source144.dtor_args;
            DAST._IType _3524___mcc_h665 = _source144.dtor_result;
            {
              RAST._IExpr _out742;
              DCOMP._IOwnership _out743;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out744;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out742, out _out743, out _out744);
              r = _out742;
              resultingOwnership = _out743;
              readIdents = _out744;
            }
          } else if (_source144.is_Primitive) {
            DAST._IPrimitive _3525___mcc_h668 = _source144.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out745;
              DCOMP._IOwnership _out746;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out747;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out745, out _out746, out _out747);
              r = _out745;
              resultingOwnership = _out746;
              readIdents = _out747;
            }
          } else if (_source144.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3526___mcc_h670 = _source144.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out748;
              DCOMP._IOwnership _out749;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out750;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out748, out _out749, out _out750);
              r = _out748;
              resultingOwnership = _out749;
              readIdents = _out750;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3527___mcc_h672 = _source144.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out751;
              DCOMP._IOwnership _out752;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out753;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out751, out _out752, out _out753);
              r = _out751;
              resultingOwnership = _out752;
              readIdents = _out753;
            }
          }
        } else if (_source124.is_SetBuilder) {
          DAST._IType _3528___mcc_h674 = _source124.dtor_element;
          DAST._IType _source146 = _3146___mcc_h1;
          if (_source146.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3529___mcc_h678 = _source146.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3530___mcc_h679 = _source146.dtor_typeArgs;
            DAST._IResolvedType _3531___mcc_h680 = _source146.dtor_resolved;
            DAST._IResolvedType _source147 = _3531___mcc_h680;
            if (_source147.is_Datatype) {
              DAST._IDatatypeType _3532___mcc_h684 = _source147.dtor_datatypeType;
              {
                RAST._IExpr _out754;
                DCOMP._IOwnership _out755;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out756;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out754, out _out755, out _out756);
                r = _out754;
                resultingOwnership = _out755;
                readIdents = _out756;
              }
            } else if (_source147.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3533___mcc_h686 = _source147.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3534___mcc_h687 = _source147.dtor_attributes;
              {
                RAST._IExpr _out757;
                DCOMP._IOwnership _out758;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out759;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out757, out _out758, out _out759);
                r = _out757;
                resultingOwnership = _out758;
                readIdents = _out759;
              }
            } else {
              DAST._IType _3535___mcc_h690 = _source147.dtor_baseType;
              DAST._INewtypeRange _3536___mcc_h691 = _source147.dtor_range;
              bool _3537___mcc_h692 = _source147.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3538___mcc_h693 = _source147.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3539_attributes = _3538___mcc_h693;
              bool _3540_erase = _3537___mcc_h692;
              DAST._INewtypeRange _3541_range = _3536___mcc_h691;
              DAST._IType _3542_b = _3535___mcc_h690;
              {
                RAST._IExpr _out760;
                DCOMP._IOwnership _out761;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out762;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out760, out _out761, out _out762);
                r = _out760;
                resultingOwnership = _out761;
                readIdents = _out762;
              }
            }
          } else if (_source146.is_Nullable) {
            DAST._IType _3543___mcc_h698 = _source146.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out763;
              DCOMP._IOwnership _out764;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out765;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out763, out _out764, out _out765);
              r = _out763;
              resultingOwnership = _out764;
              readIdents = _out765;
            }
          } else if (_source146.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3544___mcc_h700 = _source146.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out766;
              DCOMP._IOwnership _out767;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out768;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out766, out _out767, out _out768);
              r = _out766;
              resultingOwnership = _out767;
              readIdents = _out768;
            }
          } else if (_source146.is_Array) {
            DAST._IType _3545___mcc_h702 = _source146.dtor_element;
            BigInteger _3546___mcc_h703 = _source146.dtor_dims;
            {
              RAST._IExpr _out769;
              DCOMP._IOwnership _out770;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out771;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out769, out _out770, out _out771);
              r = _out769;
              resultingOwnership = _out770;
              readIdents = _out771;
            }
          } else if (_source146.is_Seq) {
            DAST._IType _3547___mcc_h706 = _source146.dtor_element;
            {
              RAST._IExpr _out772;
              DCOMP._IOwnership _out773;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out774;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out772, out _out773, out _out774);
              r = _out772;
              resultingOwnership = _out773;
              readIdents = _out774;
            }
          } else if (_source146.is_Set) {
            DAST._IType _3548___mcc_h708 = _source146.dtor_element;
            {
              RAST._IExpr _out775;
              DCOMP._IOwnership _out776;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out777;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out775, out _out776, out _out777);
              r = _out775;
              resultingOwnership = _out776;
              readIdents = _out777;
            }
          } else if (_source146.is_Multiset) {
            DAST._IType _3549___mcc_h710 = _source146.dtor_element;
            {
              RAST._IExpr _out778;
              DCOMP._IOwnership _out779;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out780;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out778, out _out779, out _out780);
              r = _out778;
              resultingOwnership = _out779;
              readIdents = _out780;
            }
          } else if (_source146.is_Map) {
            DAST._IType _3550___mcc_h712 = _source146.dtor_key;
            DAST._IType _3551___mcc_h713 = _source146.dtor_value;
            {
              RAST._IExpr _out781;
              DCOMP._IOwnership _out782;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out783;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out781, out _out782, out _out783);
              r = _out781;
              resultingOwnership = _out782;
              readIdents = _out783;
            }
          } else if (_source146.is_SetBuilder) {
            DAST._IType _3552___mcc_h716 = _source146.dtor_element;
            {
              RAST._IExpr _out784;
              DCOMP._IOwnership _out785;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out786;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out784, out _out785, out _out786);
              r = _out784;
              resultingOwnership = _out785;
              readIdents = _out786;
            }
          } else if (_source146.is_MapBuilder) {
            DAST._IType _3553___mcc_h718 = _source146.dtor_key;
            DAST._IType _3554___mcc_h719 = _source146.dtor_value;
            {
              RAST._IExpr _out787;
              DCOMP._IOwnership _out788;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out789;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out787, out _out788, out _out789);
              r = _out787;
              resultingOwnership = _out788;
              readIdents = _out789;
            }
          } else if (_source146.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3555___mcc_h722 = _source146.dtor_args;
            DAST._IType _3556___mcc_h723 = _source146.dtor_result;
            {
              RAST._IExpr _out790;
              DCOMP._IOwnership _out791;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out792;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out790, out _out791, out _out792);
              r = _out790;
              resultingOwnership = _out791;
              readIdents = _out792;
            }
          } else if (_source146.is_Primitive) {
            DAST._IPrimitive _3557___mcc_h726 = _source146.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out793;
              DCOMP._IOwnership _out794;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out795;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out793, out _out794, out _out795);
              r = _out793;
              resultingOwnership = _out794;
              readIdents = _out795;
            }
          } else if (_source146.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3558___mcc_h728 = _source146.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out796;
              DCOMP._IOwnership _out797;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out798;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out796, out _out797, out _out798);
              r = _out796;
              resultingOwnership = _out797;
              readIdents = _out798;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3559___mcc_h730 = _source146.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out799;
              DCOMP._IOwnership _out800;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out801;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out799, out _out800, out _out801);
              r = _out799;
              resultingOwnership = _out800;
              readIdents = _out801;
            }
          }
        } else if (_source124.is_MapBuilder) {
          DAST._IType _3560___mcc_h732 = _source124.dtor_key;
          DAST._IType _3561___mcc_h733 = _source124.dtor_value;
          DAST._IType _source148 = _3146___mcc_h1;
          if (_source148.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3562___mcc_h740 = _source148.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3563___mcc_h741 = _source148.dtor_typeArgs;
            DAST._IResolvedType _3564___mcc_h742 = _source148.dtor_resolved;
            DAST._IResolvedType _source149 = _3564___mcc_h742;
            if (_source149.is_Datatype) {
              DAST._IDatatypeType _3565___mcc_h746 = _source149.dtor_datatypeType;
              {
                RAST._IExpr _out802;
                DCOMP._IOwnership _out803;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out804;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out802, out _out803, out _out804);
                r = _out802;
                resultingOwnership = _out803;
                readIdents = _out804;
              }
            } else if (_source149.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3566___mcc_h748 = _source149.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3567___mcc_h749 = _source149.dtor_attributes;
              {
                RAST._IExpr _out805;
                DCOMP._IOwnership _out806;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out807;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out805, out _out806, out _out807);
                r = _out805;
                resultingOwnership = _out806;
                readIdents = _out807;
              }
            } else {
              DAST._IType _3568___mcc_h752 = _source149.dtor_baseType;
              DAST._INewtypeRange _3569___mcc_h753 = _source149.dtor_range;
              bool _3570___mcc_h754 = _source149.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3571___mcc_h755 = _source149.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3572_attributes = _3571___mcc_h755;
              bool _3573_erase = _3570___mcc_h754;
              DAST._INewtypeRange _3574_range = _3569___mcc_h753;
              DAST._IType _3575_b = _3568___mcc_h752;
              {
                RAST._IExpr _out808;
                DCOMP._IOwnership _out809;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out810;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out808, out _out809, out _out810);
                r = _out808;
                resultingOwnership = _out809;
                readIdents = _out810;
              }
            }
          } else if (_source148.is_Nullable) {
            DAST._IType _3576___mcc_h760 = _source148.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out811;
              DCOMP._IOwnership _out812;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out813;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out811, out _out812, out _out813);
              r = _out811;
              resultingOwnership = _out812;
              readIdents = _out813;
            }
          } else if (_source148.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3577___mcc_h762 = _source148.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out814;
              DCOMP._IOwnership _out815;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out816;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out814, out _out815, out _out816);
              r = _out814;
              resultingOwnership = _out815;
              readIdents = _out816;
            }
          } else if (_source148.is_Array) {
            DAST._IType _3578___mcc_h764 = _source148.dtor_element;
            BigInteger _3579___mcc_h765 = _source148.dtor_dims;
            {
              RAST._IExpr _out817;
              DCOMP._IOwnership _out818;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out819;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out817, out _out818, out _out819);
              r = _out817;
              resultingOwnership = _out818;
              readIdents = _out819;
            }
          } else if (_source148.is_Seq) {
            DAST._IType _3580___mcc_h768 = _source148.dtor_element;
            {
              RAST._IExpr _out820;
              DCOMP._IOwnership _out821;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out822;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out820, out _out821, out _out822);
              r = _out820;
              resultingOwnership = _out821;
              readIdents = _out822;
            }
          } else if (_source148.is_Set) {
            DAST._IType _3581___mcc_h770 = _source148.dtor_element;
            {
              RAST._IExpr _out823;
              DCOMP._IOwnership _out824;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out825;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out823, out _out824, out _out825);
              r = _out823;
              resultingOwnership = _out824;
              readIdents = _out825;
            }
          } else if (_source148.is_Multiset) {
            DAST._IType _3582___mcc_h772 = _source148.dtor_element;
            {
              RAST._IExpr _out826;
              DCOMP._IOwnership _out827;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out828;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out826, out _out827, out _out828);
              r = _out826;
              resultingOwnership = _out827;
              readIdents = _out828;
            }
          } else if (_source148.is_Map) {
            DAST._IType _3583___mcc_h774 = _source148.dtor_key;
            DAST._IType _3584___mcc_h775 = _source148.dtor_value;
            {
              RAST._IExpr _out829;
              DCOMP._IOwnership _out830;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out831;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out829, out _out830, out _out831);
              r = _out829;
              resultingOwnership = _out830;
              readIdents = _out831;
            }
          } else if (_source148.is_SetBuilder) {
            DAST._IType _3585___mcc_h778 = _source148.dtor_element;
            {
              RAST._IExpr _out832;
              DCOMP._IOwnership _out833;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out834;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out832, out _out833, out _out834);
              r = _out832;
              resultingOwnership = _out833;
              readIdents = _out834;
            }
          } else if (_source148.is_MapBuilder) {
            DAST._IType _3586___mcc_h780 = _source148.dtor_key;
            DAST._IType _3587___mcc_h781 = _source148.dtor_value;
            {
              RAST._IExpr _out835;
              DCOMP._IOwnership _out836;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out837;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out835, out _out836, out _out837);
              r = _out835;
              resultingOwnership = _out836;
              readIdents = _out837;
            }
          } else if (_source148.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3588___mcc_h784 = _source148.dtor_args;
            DAST._IType _3589___mcc_h785 = _source148.dtor_result;
            {
              RAST._IExpr _out838;
              DCOMP._IOwnership _out839;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out840;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out838, out _out839, out _out840);
              r = _out838;
              resultingOwnership = _out839;
              readIdents = _out840;
            }
          } else if (_source148.is_Primitive) {
            DAST._IPrimitive _3590___mcc_h788 = _source148.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out841;
              DCOMP._IOwnership _out842;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out843;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out841, out _out842, out _out843);
              r = _out841;
              resultingOwnership = _out842;
              readIdents = _out843;
            }
          } else if (_source148.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3591___mcc_h790 = _source148.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out844;
              DCOMP._IOwnership _out845;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out846;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out844, out _out845, out _out846);
              r = _out844;
              resultingOwnership = _out845;
              readIdents = _out846;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3592___mcc_h792 = _source148.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out847;
              DCOMP._IOwnership _out848;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out849;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out847, out _out848, out _out849);
              r = _out847;
              resultingOwnership = _out848;
              readIdents = _out849;
            }
          }
        } else if (_source124.is_Arrow) {
          Dafny.ISequence<DAST._IType> _3593___mcc_h794 = _source124.dtor_args;
          DAST._IType _3594___mcc_h795 = _source124.dtor_result;
          DAST._IType _source150 = _3146___mcc_h1;
          if (_source150.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3595___mcc_h802 = _source150.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3596___mcc_h803 = _source150.dtor_typeArgs;
            DAST._IResolvedType _3597___mcc_h804 = _source150.dtor_resolved;
            DAST._IResolvedType _source151 = _3597___mcc_h804;
            if (_source151.is_Datatype) {
              DAST._IDatatypeType _3598___mcc_h808 = _source151.dtor_datatypeType;
              {
                RAST._IExpr _out850;
                DCOMP._IOwnership _out851;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out852;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out850, out _out851, out _out852);
                r = _out850;
                resultingOwnership = _out851;
                readIdents = _out852;
              }
            } else if (_source151.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3599___mcc_h810 = _source151.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3600___mcc_h811 = _source151.dtor_attributes;
              {
                RAST._IExpr _out853;
                DCOMP._IOwnership _out854;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out855;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out853, out _out854, out _out855);
                r = _out853;
                resultingOwnership = _out854;
                readIdents = _out855;
              }
            } else {
              DAST._IType _3601___mcc_h814 = _source151.dtor_baseType;
              DAST._INewtypeRange _3602___mcc_h815 = _source151.dtor_range;
              bool _3603___mcc_h816 = _source151.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3604___mcc_h817 = _source151.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3605_attributes = _3604___mcc_h817;
              bool _3606_erase = _3603___mcc_h816;
              DAST._INewtypeRange _3607_range = _3602___mcc_h815;
              DAST._IType _3608_b = _3601___mcc_h814;
              {
                RAST._IExpr _out856;
                DCOMP._IOwnership _out857;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out858;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out856, out _out857, out _out858);
                r = _out856;
                resultingOwnership = _out857;
                readIdents = _out858;
              }
            }
          } else if (_source150.is_Nullable) {
            DAST._IType _3609___mcc_h822 = _source150.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out859;
              DCOMP._IOwnership _out860;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out861;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out859, out _out860, out _out861);
              r = _out859;
              resultingOwnership = _out860;
              readIdents = _out861;
            }
          } else if (_source150.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3610___mcc_h824 = _source150.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out862;
              DCOMP._IOwnership _out863;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out864;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out862, out _out863, out _out864);
              r = _out862;
              resultingOwnership = _out863;
              readIdents = _out864;
            }
          } else if (_source150.is_Array) {
            DAST._IType _3611___mcc_h826 = _source150.dtor_element;
            BigInteger _3612___mcc_h827 = _source150.dtor_dims;
            {
              RAST._IExpr _out865;
              DCOMP._IOwnership _out866;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out867;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out865, out _out866, out _out867);
              r = _out865;
              resultingOwnership = _out866;
              readIdents = _out867;
            }
          } else if (_source150.is_Seq) {
            DAST._IType _3613___mcc_h830 = _source150.dtor_element;
            {
              RAST._IExpr _out868;
              DCOMP._IOwnership _out869;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out870;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out868, out _out869, out _out870);
              r = _out868;
              resultingOwnership = _out869;
              readIdents = _out870;
            }
          } else if (_source150.is_Set) {
            DAST._IType _3614___mcc_h832 = _source150.dtor_element;
            {
              RAST._IExpr _out871;
              DCOMP._IOwnership _out872;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out873;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out871, out _out872, out _out873);
              r = _out871;
              resultingOwnership = _out872;
              readIdents = _out873;
            }
          } else if (_source150.is_Multiset) {
            DAST._IType _3615___mcc_h834 = _source150.dtor_element;
            {
              RAST._IExpr _out874;
              DCOMP._IOwnership _out875;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out876;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out874, out _out875, out _out876);
              r = _out874;
              resultingOwnership = _out875;
              readIdents = _out876;
            }
          } else if (_source150.is_Map) {
            DAST._IType _3616___mcc_h836 = _source150.dtor_key;
            DAST._IType _3617___mcc_h837 = _source150.dtor_value;
            {
              RAST._IExpr _out877;
              DCOMP._IOwnership _out878;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out879;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out877, out _out878, out _out879);
              r = _out877;
              resultingOwnership = _out878;
              readIdents = _out879;
            }
          } else if (_source150.is_SetBuilder) {
            DAST._IType _3618___mcc_h840 = _source150.dtor_element;
            {
              RAST._IExpr _out880;
              DCOMP._IOwnership _out881;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out882;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out880, out _out881, out _out882);
              r = _out880;
              resultingOwnership = _out881;
              readIdents = _out882;
            }
          } else if (_source150.is_MapBuilder) {
            DAST._IType _3619___mcc_h842 = _source150.dtor_key;
            DAST._IType _3620___mcc_h843 = _source150.dtor_value;
            {
              RAST._IExpr _out883;
              DCOMP._IOwnership _out884;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out885;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out883, out _out884, out _out885);
              r = _out883;
              resultingOwnership = _out884;
              readIdents = _out885;
            }
          } else if (_source150.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3621___mcc_h846 = _source150.dtor_args;
            DAST._IType _3622___mcc_h847 = _source150.dtor_result;
            {
              RAST._IExpr _out886;
              DCOMP._IOwnership _out887;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out888;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out886, out _out887, out _out888);
              r = _out886;
              resultingOwnership = _out887;
              readIdents = _out888;
            }
          } else if (_source150.is_Primitive) {
            DAST._IPrimitive _3623___mcc_h850 = _source150.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out889;
              DCOMP._IOwnership _out890;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out891;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out889, out _out890, out _out891);
              r = _out889;
              resultingOwnership = _out890;
              readIdents = _out891;
            }
          } else if (_source150.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3624___mcc_h852 = _source150.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out892;
              DCOMP._IOwnership _out893;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out894;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out892, out _out893, out _out894);
              r = _out892;
              resultingOwnership = _out893;
              readIdents = _out894;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3625___mcc_h854 = _source150.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out895;
              DCOMP._IOwnership _out896;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out897;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out895, out _out896, out _out897);
              r = _out895;
              resultingOwnership = _out896;
              readIdents = _out897;
            }
          }
        } else if (_source124.is_Primitive) {
          DAST._IPrimitive _3626___mcc_h856 = _source124.dtor_Primitive_i_a0;
          DAST._IPrimitive _source152 = _3626___mcc_h856;
          if (_source152.is_Int) {
            DAST._IType _source153 = _3146___mcc_h1;
            if (_source153.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3627___mcc_h860 = _source153.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3628___mcc_h861 = _source153.dtor_typeArgs;
              DAST._IResolvedType _3629___mcc_h862 = _source153.dtor_resolved;
              DAST._IResolvedType _source154 = _3629___mcc_h862;
              if (_source154.is_Datatype) {
                DAST._IDatatypeType _3630___mcc_h866 = _source154.dtor_datatypeType;
                {
                  RAST._IExpr _out898;
                  DCOMP._IOwnership _out899;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out900;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out898, out _out899, out _out900);
                  r = _out898;
                  resultingOwnership = _out899;
                  readIdents = _out900;
                }
              } else if (_source154.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3631___mcc_h868 = _source154.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3632___mcc_h869 = _source154.dtor_attributes;
                {
                  RAST._IExpr _out901;
                  DCOMP._IOwnership _out902;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out903;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out901, out _out902, out _out903);
                  r = _out901;
                  resultingOwnership = _out902;
                  readIdents = _out903;
                }
              } else {
                DAST._IType _3633___mcc_h872 = _source154.dtor_baseType;
                DAST._INewtypeRange _3634___mcc_h873 = _source154.dtor_range;
                bool _3635___mcc_h874 = _source154.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3636___mcc_h875 = _source154.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3637_attributes = _3636___mcc_h875;
                bool _3638_erase = _3635___mcc_h874;
                DAST._INewtypeRange _3639_range = _3634___mcc_h873;
                DAST._IType _3640_b = _3633___mcc_h872;
                {
                  RAST._IExpr _out904;
                  DCOMP._IOwnership _out905;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out906;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out904, out _out905, out _out906);
                  r = _out904;
                  resultingOwnership = _out905;
                  readIdents = _out906;
                }
              }
            } else if (_source153.is_Nullable) {
              DAST._IType _3641___mcc_h880 = _source153.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out907;
                DCOMP._IOwnership _out908;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out909;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out907, out _out908, out _out909);
                r = _out907;
                resultingOwnership = _out908;
                readIdents = _out909;
              }
            } else if (_source153.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3642___mcc_h882 = _source153.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out910;
                DCOMP._IOwnership _out911;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out912;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out910, out _out911, out _out912);
                r = _out910;
                resultingOwnership = _out911;
                readIdents = _out912;
              }
            } else if (_source153.is_Array) {
              DAST._IType _3643___mcc_h884 = _source153.dtor_element;
              BigInteger _3644___mcc_h885 = _source153.dtor_dims;
              {
                RAST._IExpr _out913;
                DCOMP._IOwnership _out914;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out915;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out913, out _out914, out _out915);
                r = _out913;
                resultingOwnership = _out914;
                readIdents = _out915;
              }
            } else if (_source153.is_Seq) {
              DAST._IType _3645___mcc_h888 = _source153.dtor_element;
              {
                RAST._IExpr _out916;
                DCOMP._IOwnership _out917;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out918;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out916, out _out917, out _out918);
                r = _out916;
                resultingOwnership = _out917;
                readIdents = _out918;
              }
            } else if (_source153.is_Set) {
              DAST._IType _3646___mcc_h890 = _source153.dtor_element;
              {
                RAST._IExpr _out919;
                DCOMP._IOwnership _out920;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out921;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out919, out _out920, out _out921);
                r = _out919;
                resultingOwnership = _out920;
                readIdents = _out921;
              }
            } else if (_source153.is_Multiset) {
              DAST._IType _3647___mcc_h892 = _source153.dtor_element;
              {
                RAST._IExpr _out922;
                DCOMP._IOwnership _out923;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out924;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out922, out _out923, out _out924);
                r = _out922;
                resultingOwnership = _out923;
                readIdents = _out924;
              }
            } else if (_source153.is_Map) {
              DAST._IType _3648___mcc_h894 = _source153.dtor_key;
              DAST._IType _3649___mcc_h895 = _source153.dtor_value;
              {
                RAST._IExpr _out925;
                DCOMP._IOwnership _out926;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out927;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out925, out _out926, out _out927);
                r = _out925;
                resultingOwnership = _out926;
                readIdents = _out927;
              }
            } else if (_source153.is_SetBuilder) {
              DAST._IType _3650___mcc_h898 = _source153.dtor_element;
              {
                RAST._IExpr _out928;
                DCOMP._IOwnership _out929;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out930;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out928, out _out929, out _out930);
                r = _out928;
                resultingOwnership = _out929;
                readIdents = _out930;
              }
            } else if (_source153.is_MapBuilder) {
              DAST._IType _3651___mcc_h900 = _source153.dtor_key;
              DAST._IType _3652___mcc_h901 = _source153.dtor_value;
              {
                RAST._IExpr _out931;
                DCOMP._IOwnership _out932;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out933;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out931, out _out932, out _out933);
                r = _out931;
                resultingOwnership = _out932;
                readIdents = _out933;
              }
            } else if (_source153.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3653___mcc_h904 = _source153.dtor_args;
              DAST._IType _3654___mcc_h905 = _source153.dtor_result;
              {
                RAST._IExpr _out934;
                DCOMP._IOwnership _out935;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out936;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out934, out _out935, out _out936);
                r = _out934;
                resultingOwnership = _out935;
                readIdents = _out936;
              }
            } else if (_source153.is_Primitive) {
              DAST._IPrimitive _3655___mcc_h908 = _source153.dtor_Primitive_i_a0;
              DAST._IPrimitive _source155 = _3655___mcc_h908;
              if (_source155.is_Int) {
                {
                  RAST._IExpr _out937;
                  DCOMP._IOwnership _out938;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out939;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out937, out _out938, out _out939);
                  r = _out937;
                  resultingOwnership = _out938;
                  readIdents = _out939;
                }
              } else if (_source155.is_Real) {
                {
                  RAST._IExpr _3656_recursiveGen;
                  DCOMP._IOwnership _3657___v91;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3658_recIdents;
                  RAST._IExpr _out940;
                  DCOMP._IOwnership _out941;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out942;
                  (this).GenExpr(_3139_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out940, out _out941, out _out942);
                  _3656_recursiveGen = _out940;
                  _3657___v91 = _out941;
                  _3658_recIdents = _out942;
                  r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_3656_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                  RAST._IExpr _out943;
                  DCOMP._IOwnership _out944;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out943, out _out944);
                  r = _out943;
                  resultingOwnership = _out944;
                  readIdents = _3658_recIdents;
                }
              } else if (_source155.is_String) {
                {
                  RAST._IExpr _out945;
                  DCOMP._IOwnership _out946;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out947;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out945, out _out946, out _out947);
                  r = _out945;
                  resultingOwnership = _out946;
                  readIdents = _out947;
                }
              } else if (_source155.is_Bool) {
                {
                  RAST._IExpr _out948;
                  DCOMP._IOwnership _out949;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out950;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out948, out _out949, out _out950);
                  r = _out948;
                  resultingOwnership = _out949;
                  readIdents = _out950;
                }
              } else {
                {
                  RAST._IType _3659_rhsType;
                  RAST._IType _out951;
                  _out951 = (this).GenType(_3141_toTpe, true, false);
                  _3659_rhsType = _out951;
                  RAST._IExpr _3660_recursiveGen;
                  DCOMP._IOwnership _3661___v97;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3662_recIdents;
                  RAST._IExpr _out952;
                  DCOMP._IOwnership _out953;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out954;
                  (this).GenExpr(_3139_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out952, out _out953, out _out954);
                  _3660_recursiveGen = _out952;
                  _3661___v97 = _out953;
                  _3662_recIdents = _out954;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), (_3660_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()")));
                  RAST._IExpr _out955;
                  DCOMP._IOwnership _out956;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out955, out _out956);
                  r = _out955;
                  resultingOwnership = _out956;
                  readIdents = _3662_recIdents;
                }
              }
            } else if (_source153.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3663___mcc_h910 = _source153.dtor_Passthrough_i_a0;
              {
                RAST._IType _3664_rhsType;
                RAST._IType _out957;
                _out957 = (this).GenType(_3141_toTpe, true, false);
                _3664_rhsType = _out957;
                RAST._IExpr _3665_recursiveGen;
                DCOMP._IOwnership _3666___v94;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3667_recIdents;
                RAST._IExpr _out958;
                DCOMP._IOwnership _out959;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out960;
                (this).GenExpr(_3139_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out958, out _out959, out _out960);
                _3665_recursiveGen = _out958;
                _3666___v94 = _out959;
                _3667_recIdents = _out960;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3664_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_3665_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                RAST._IExpr _out961;
                DCOMP._IOwnership _out962;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out961, out _out962);
                r = _out961;
                resultingOwnership = _out962;
                readIdents = _3667_recIdents;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3668___mcc_h912 = _source153.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out963;
                DCOMP._IOwnership _out964;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out965;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out963, out _out964, out _out965);
                r = _out963;
                resultingOwnership = _out964;
                readIdents = _out965;
              }
            }
          } else if (_source152.is_Real) {
            DAST._IType _source156 = _3146___mcc_h1;
            if (_source156.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3669___mcc_h914 = _source156.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3670___mcc_h915 = _source156.dtor_typeArgs;
              DAST._IResolvedType _3671___mcc_h916 = _source156.dtor_resolved;
              DAST._IResolvedType _source157 = _3671___mcc_h916;
              if (_source157.is_Datatype) {
                DAST._IDatatypeType _3672___mcc_h920 = _source157.dtor_datatypeType;
                {
                  RAST._IExpr _out966;
                  DCOMP._IOwnership _out967;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out968;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out966, out _out967, out _out968);
                  r = _out966;
                  resultingOwnership = _out967;
                  readIdents = _out968;
                }
              } else if (_source157.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3673___mcc_h922 = _source157.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3674___mcc_h923 = _source157.dtor_attributes;
                {
                  RAST._IExpr _out969;
                  DCOMP._IOwnership _out970;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out971;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out969, out _out970, out _out971);
                  r = _out969;
                  resultingOwnership = _out970;
                  readIdents = _out971;
                }
              } else {
                DAST._IType _3675___mcc_h926 = _source157.dtor_baseType;
                DAST._INewtypeRange _3676___mcc_h927 = _source157.dtor_range;
                bool _3677___mcc_h928 = _source157.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3678___mcc_h929 = _source157.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3679_attributes = _3678___mcc_h929;
                bool _3680_erase = _3677___mcc_h928;
                DAST._INewtypeRange _3681_range = _3676___mcc_h927;
                DAST._IType _3682_b = _3675___mcc_h926;
                {
                  RAST._IExpr _out972;
                  DCOMP._IOwnership _out973;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out972, out _out973, out _out974);
                  r = _out972;
                  resultingOwnership = _out973;
                  readIdents = _out974;
                }
              }
            } else if (_source156.is_Nullable) {
              DAST._IType _3683___mcc_h934 = _source156.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out975;
                DCOMP._IOwnership _out976;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out977;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out975, out _out976, out _out977);
                r = _out975;
                resultingOwnership = _out976;
                readIdents = _out977;
              }
            } else if (_source156.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3684___mcc_h936 = _source156.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out978;
                DCOMP._IOwnership _out979;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out980;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out978, out _out979, out _out980);
                r = _out978;
                resultingOwnership = _out979;
                readIdents = _out980;
              }
            } else if (_source156.is_Array) {
              DAST._IType _3685___mcc_h938 = _source156.dtor_element;
              BigInteger _3686___mcc_h939 = _source156.dtor_dims;
              {
                RAST._IExpr _out981;
                DCOMP._IOwnership _out982;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out983;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out981, out _out982, out _out983);
                r = _out981;
                resultingOwnership = _out982;
                readIdents = _out983;
              }
            } else if (_source156.is_Seq) {
              DAST._IType _3687___mcc_h942 = _source156.dtor_element;
              {
                RAST._IExpr _out984;
                DCOMP._IOwnership _out985;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out986;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out984, out _out985, out _out986);
                r = _out984;
                resultingOwnership = _out985;
                readIdents = _out986;
              }
            } else if (_source156.is_Set) {
              DAST._IType _3688___mcc_h944 = _source156.dtor_element;
              {
                RAST._IExpr _out987;
                DCOMP._IOwnership _out988;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out989;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out987, out _out988, out _out989);
                r = _out987;
                resultingOwnership = _out988;
                readIdents = _out989;
              }
            } else if (_source156.is_Multiset) {
              DAST._IType _3689___mcc_h946 = _source156.dtor_element;
              {
                RAST._IExpr _out990;
                DCOMP._IOwnership _out991;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out992;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out990, out _out991, out _out992);
                r = _out990;
                resultingOwnership = _out991;
                readIdents = _out992;
              }
            } else if (_source156.is_Map) {
              DAST._IType _3690___mcc_h948 = _source156.dtor_key;
              DAST._IType _3691___mcc_h949 = _source156.dtor_value;
              {
                RAST._IExpr _out993;
                DCOMP._IOwnership _out994;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out995;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out993, out _out994, out _out995);
                r = _out993;
                resultingOwnership = _out994;
                readIdents = _out995;
              }
            } else if (_source156.is_SetBuilder) {
              DAST._IType _3692___mcc_h952 = _source156.dtor_element;
              {
                RAST._IExpr _out996;
                DCOMP._IOwnership _out997;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out998;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out996, out _out997, out _out998);
                r = _out996;
                resultingOwnership = _out997;
                readIdents = _out998;
              }
            } else if (_source156.is_MapBuilder) {
              DAST._IType _3693___mcc_h954 = _source156.dtor_key;
              DAST._IType _3694___mcc_h955 = _source156.dtor_value;
              {
                RAST._IExpr _out999;
                DCOMP._IOwnership _out1000;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1001;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out999, out _out1000, out _out1001);
                r = _out999;
                resultingOwnership = _out1000;
                readIdents = _out1001;
              }
            } else if (_source156.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3695___mcc_h958 = _source156.dtor_args;
              DAST._IType _3696___mcc_h959 = _source156.dtor_result;
              {
                RAST._IExpr _out1002;
                DCOMP._IOwnership _out1003;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1004;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1002, out _out1003, out _out1004);
                r = _out1002;
                resultingOwnership = _out1003;
                readIdents = _out1004;
              }
            } else if (_source156.is_Primitive) {
              DAST._IPrimitive _3697___mcc_h962 = _source156.dtor_Primitive_i_a0;
              DAST._IPrimitive _source158 = _3697___mcc_h962;
              if (_source158.is_Int) {
                {
                  RAST._IExpr _3698_recursiveGen;
                  DCOMP._IOwnership _3699___v92;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3700_recIdents;
                  RAST._IExpr _out1005;
                  DCOMP._IOwnership _out1006;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1007;
                  (this).GenExpr(_3139_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1005, out _out1006, out _out1007);
                  _3698_recursiveGen = _out1005;
                  _3699___v92 = _out1006;
                  _3700_recIdents = _out1007;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_3698_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                  RAST._IExpr _out1008;
                  DCOMP._IOwnership _out1009;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1008, out _out1009);
                  r = _out1008;
                  resultingOwnership = _out1009;
                  readIdents = _3700_recIdents;
                }
              } else if (_source158.is_Real) {
                {
                  RAST._IExpr _out1010;
                  DCOMP._IOwnership _out1011;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1012;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1010, out _out1011, out _out1012);
                  r = _out1010;
                  resultingOwnership = _out1011;
                  readIdents = _out1012;
                }
              } else if (_source158.is_String) {
                {
                  RAST._IExpr _out1013;
                  DCOMP._IOwnership _out1014;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1015;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1013, out _out1014, out _out1015);
                  r = _out1013;
                  resultingOwnership = _out1014;
                  readIdents = _out1015;
                }
              } else if (_source158.is_Bool) {
                {
                  RAST._IExpr _out1016;
                  DCOMP._IOwnership _out1017;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1018;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1016, out _out1017, out _out1018);
                  r = _out1016;
                  resultingOwnership = _out1017;
                  readIdents = _out1018;
                }
              } else {
                {
                  RAST._IExpr _out1019;
                  DCOMP._IOwnership _out1020;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1021;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1019, out _out1020, out _out1021);
                  r = _out1019;
                  resultingOwnership = _out1020;
                  readIdents = _out1021;
                }
              }
            } else if (_source156.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3701___mcc_h964 = _source156.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1022;
                DCOMP._IOwnership _out1023;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1024;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1022, out _out1023, out _out1024);
                r = _out1022;
                resultingOwnership = _out1023;
                readIdents = _out1024;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3702___mcc_h966 = _source156.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1025;
                DCOMP._IOwnership _out1026;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1027;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1025, out _out1026, out _out1027);
                r = _out1025;
                resultingOwnership = _out1026;
                readIdents = _out1027;
              }
            }
          } else if (_source152.is_String) {
            DAST._IType _source159 = _3146___mcc_h1;
            if (_source159.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3703___mcc_h968 = _source159.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3704___mcc_h969 = _source159.dtor_typeArgs;
              DAST._IResolvedType _3705___mcc_h970 = _source159.dtor_resolved;
              DAST._IResolvedType _source160 = _3705___mcc_h970;
              if (_source160.is_Datatype) {
                DAST._IDatatypeType _3706___mcc_h974 = _source160.dtor_datatypeType;
                {
                  RAST._IExpr _out1028;
                  DCOMP._IOwnership _out1029;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1030;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1028, out _out1029, out _out1030);
                  r = _out1028;
                  resultingOwnership = _out1029;
                  readIdents = _out1030;
                }
              } else if (_source160.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3707___mcc_h976 = _source160.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3708___mcc_h977 = _source160.dtor_attributes;
                {
                  RAST._IExpr _out1031;
                  DCOMP._IOwnership _out1032;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1033;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1031, out _out1032, out _out1033);
                  r = _out1031;
                  resultingOwnership = _out1032;
                  readIdents = _out1033;
                }
              } else {
                DAST._IType _3709___mcc_h980 = _source160.dtor_baseType;
                DAST._INewtypeRange _3710___mcc_h981 = _source160.dtor_range;
                bool _3711___mcc_h982 = _source160.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3712___mcc_h983 = _source160.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3713_attributes = _3712___mcc_h983;
                bool _3714_erase = _3711___mcc_h982;
                DAST._INewtypeRange _3715_range = _3710___mcc_h981;
                DAST._IType _3716_b = _3709___mcc_h980;
                {
                  RAST._IExpr _out1034;
                  DCOMP._IOwnership _out1035;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1036;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1034, out _out1035, out _out1036);
                  r = _out1034;
                  resultingOwnership = _out1035;
                  readIdents = _out1036;
                }
              }
            } else if (_source159.is_Nullable) {
              DAST._IType _3717___mcc_h988 = _source159.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1037;
                DCOMP._IOwnership _out1038;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1039;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1037, out _out1038, out _out1039);
                r = _out1037;
                resultingOwnership = _out1038;
                readIdents = _out1039;
              }
            } else if (_source159.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3718___mcc_h990 = _source159.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1040;
                DCOMP._IOwnership _out1041;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1042;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1040, out _out1041, out _out1042);
                r = _out1040;
                resultingOwnership = _out1041;
                readIdents = _out1042;
              }
            } else if (_source159.is_Array) {
              DAST._IType _3719___mcc_h992 = _source159.dtor_element;
              BigInteger _3720___mcc_h993 = _source159.dtor_dims;
              {
                RAST._IExpr _out1043;
                DCOMP._IOwnership _out1044;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1045;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1043, out _out1044, out _out1045);
                r = _out1043;
                resultingOwnership = _out1044;
                readIdents = _out1045;
              }
            } else if (_source159.is_Seq) {
              DAST._IType _3721___mcc_h996 = _source159.dtor_element;
              {
                RAST._IExpr _out1046;
                DCOMP._IOwnership _out1047;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1048;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1046, out _out1047, out _out1048);
                r = _out1046;
                resultingOwnership = _out1047;
                readIdents = _out1048;
              }
            } else if (_source159.is_Set) {
              DAST._IType _3722___mcc_h998 = _source159.dtor_element;
              {
                RAST._IExpr _out1049;
                DCOMP._IOwnership _out1050;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1051;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1049, out _out1050, out _out1051);
                r = _out1049;
                resultingOwnership = _out1050;
                readIdents = _out1051;
              }
            } else if (_source159.is_Multiset) {
              DAST._IType _3723___mcc_h1000 = _source159.dtor_element;
              {
                RAST._IExpr _out1052;
                DCOMP._IOwnership _out1053;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1054;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1052, out _out1053, out _out1054);
                r = _out1052;
                resultingOwnership = _out1053;
                readIdents = _out1054;
              }
            } else if (_source159.is_Map) {
              DAST._IType _3724___mcc_h1002 = _source159.dtor_key;
              DAST._IType _3725___mcc_h1003 = _source159.dtor_value;
              {
                RAST._IExpr _out1055;
                DCOMP._IOwnership _out1056;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1057;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1055, out _out1056, out _out1057);
                r = _out1055;
                resultingOwnership = _out1056;
                readIdents = _out1057;
              }
            } else if (_source159.is_SetBuilder) {
              DAST._IType _3726___mcc_h1006 = _source159.dtor_element;
              {
                RAST._IExpr _out1058;
                DCOMP._IOwnership _out1059;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1060;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1058, out _out1059, out _out1060);
                r = _out1058;
                resultingOwnership = _out1059;
                readIdents = _out1060;
              }
            } else if (_source159.is_MapBuilder) {
              DAST._IType _3727___mcc_h1008 = _source159.dtor_key;
              DAST._IType _3728___mcc_h1009 = _source159.dtor_value;
              {
                RAST._IExpr _out1061;
                DCOMP._IOwnership _out1062;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1063;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1061, out _out1062, out _out1063);
                r = _out1061;
                resultingOwnership = _out1062;
                readIdents = _out1063;
              }
            } else if (_source159.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3729___mcc_h1012 = _source159.dtor_args;
              DAST._IType _3730___mcc_h1013 = _source159.dtor_result;
              {
                RAST._IExpr _out1064;
                DCOMP._IOwnership _out1065;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1066;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1064, out _out1065, out _out1066);
                r = _out1064;
                resultingOwnership = _out1065;
                readIdents = _out1066;
              }
            } else if (_source159.is_Primitive) {
              DAST._IPrimitive _3731___mcc_h1016 = _source159.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out1067;
                DCOMP._IOwnership _out1068;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1069;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1067, out _out1068, out _out1069);
                r = _out1067;
                resultingOwnership = _out1068;
                readIdents = _out1069;
              }
            } else if (_source159.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3732___mcc_h1018 = _source159.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1070;
                DCOMP._IOwnership _out1071;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1072;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1070, out _out1071, out _out1072);
                r = _out1070;
                resultingOwnership = _out1071;
                readIdents = _out1072;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3733___mcc_h1020 = _source159.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1073;
                DCOMP._IOwnership _out1074;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1075;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1073, out _out1074, out _out1075);
                r = _out1073;
                resultingOwnership = _out1074;
                readIdents = _out1075;
              }
            }
          } else if (_source152.is_Bool) {
            DAST._IType _source161 = _3146___mcc_h1;
            if (_source161.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3734___mcc_h1022 = _source161.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3735___mcc_h1023 = _source161.dtor_typeArgs;
              DAST._IResolvedType _3736___mcc_h1024 = _source161.dtor_resolved;
              DAST._IResolvedType _source162 = _3736___mcc_h1024;
              if (_source162.is_Datatype) {
                DAST._IDatatypeType _3737___mcc_h1028 = _source162.dtor_datatypeType;
                {
                  RAST._IExpr _out1076;
                  DCOMP._IOwnership _out1077;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1078;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1076, out _out1077, out _out1078);
                  r = _out1076;
                  resultingOwnership = _out1077;
                  readIdents = _out1078;
                }
              } else if (_source162.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3738___mcc_h1030 = _source162.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3739___mcc_h1031 = _source162.dtor_attributes;
                {
                  RAST._IExpr _out1079;
                  DCOMP._IOwnership _out1080;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1081;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1079, out _out1080, out _out1081);
                  r = _out1079;
                  resultingOwnership = _out1080;
                  readIdents = _out1081;
                }
              } else {
                DAST._IType _3740___mcc_h1034 = _source162.dtor_baseType;
                DAST._INewtypeRange _3741___mcc_h1035 = _source162.dtor_range;
                bool _3742___mcc_h1036 = _source162.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3743___mcc_h1037 = _source162.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3744_attributes = _3743___mcc_h1037;
                bool _3745_erase = _3742___mcc_h1036;
                DAST._INewtypeRange _3746_range = _3741___mcc_h1035;
                DAST._IType _3747_b = _3740___mcc_h1034;
                {
                  RAST._IExpr _out1082;
                  DCOMP._IOwnership _out1083;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1084;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1082, out _out1083, out _out1084);
                  r = _out1082;
                  resultingOwnership = _out1083;
                  readIdents = _out1084;
                }
              }
            } else if (_source161.is_Nullable) {
              DAST._IType _3748___mcc_h1042 = _source161.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1085;
                DCOMP._IOwnership _out1086;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1087;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1085, out _out1086, out _out1087);
                r = _out1085;
                resultingOwnership = _out1086;
                readIdents = _out1087;
              }
            } else if (_source161.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3749___mcc_h1044 = _source161.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1088;
                DCOMP._IOwnership _out1089;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1090;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1088, out _out1089, out _out1090);
                r = _out1088;
                resultingOwnership = _out1089;
                readIdents = _out1090;
              }
            } else if (_source161.is_Array) {
              DAST._IType _3750___mcc_h1046 = _source161.dtor_element;
              BigInteger _3751___mcc_h1047 = _source161.dtor_dims;
              {
                RAST._IExpr _out1091;
                DCOMP._IOwnership _out1092;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1093;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1091, out _out1092, out _out1093);
                r = _out1091;
                resultingOwnership = _out1092;
                readIdents = _out1093;
              }
            } else if (_source161.is_Seq) {
              DAST._IType _3752___mcc_h1050 = _source161.dtor_element;
              {
                RAST._IExpr _out1094;
                DCOMP._IOwnership _out1095;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1096;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1094, out _out1095, out _out1096);
                r = _out1094;
                resultingOwnership = _out1095;
                readIdents = _out1096;
              }
            } else if (_source161.is_Set) {
              DAST._IType _3753___mcc_h1052 = _source161.dtor_element;
              {
                RAST._IExpr _out1097;
                DCOMP._IOwnership _out1098;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1099;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1097, out _out1098, out _out1099);
                r = _out1097;
                resultingOwnership = _out1098;
                readIdents = _out1099;
              }
            } else if (_source161.is_Multiset) {
              DAST._IType _3754___mcc_h1054 = _source161.dtor_element;
              {
                RAST._IExpr _out1100;
                DCOMP._IOwnership _out1101;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1102;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1100, out _out1101, out _out1102);
                r = _out1100;
                resultingOwnership = _out1101;
                readIdents = _out1102;
              }
            } else if (_source161.is_Map) {
              DAST._IType _3755___mcc_h1056 = _source161.dtor_key;
              DAST._IType _3756___mcc_h1057 = _source161.dtor_value;
              {
                RAST._IExpr _out1103;
                DCOMP._IOwnership _out1104;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1105;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1103, out _out1104, out _out1105);
                r = _out1103;
                resultingOwnership = _out1104;
                readIdents = _out1105;
              }
            } else if (_source161.is_SetBuilder) {
              DAST._IType _3757___mcc_h1060 = _source161.dtor_element;
              {
                RAST._IExpr _out1106;
                DCOMP._IOwnership _out1107;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1108;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1106, out _out1107, out _out1108);
                r = _out1106;
                resultingOwnership = _out1107;
                readIdents = _out1108;
              }
            } else if (_source161.is_MapBuilder) {
              DAST._IType _3758___mcc_h1062 = _source161.dtor_key;
              DAST._IType _3759___mcc_h1063 = _source161.dtor_value;
              {
                RAST._IExpr _out1109;
                DCOMP._IOwnership _out1110;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1111;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1109, out _out1110, out _out1111);
                r = _out1109;
                resultingOwnership = _out1110;
                readIdents = _out1111;
              }
            } else if (_source161.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3760___mcc_h1066 = _source161.dtor_args;
              DAST._IType _3761___mcc_h1067 = _source161.dtor_result;
              {
                RAST._IExpr _out1112;
                DCOMP._IOwnership _out1113;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1114;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1112, out _out1113, out _out1114);
                r = _out1112;
                resultingOwnership = _out1113;
                readIdents = _out1114;
              }
            } else if (_source161.is_Primitive) {
              DAST._IPrimitive _3762___mcc_h1070 = _source161.dtor_Primitive_i_a0;
              {
                RAST._IExpr _out1115;
                DCOMP._IOwnership _out1116;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1117;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1115, out _out1116, out _out1117);
                r = _out1115;
                resultingOwnership = _out1116;
                readIdents = _out1117;
              }
            } else if (_source161.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3763___mcc_h1072 = _source161.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1118;
                DCOMP._IOwnership _out1119;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1120;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1118, out _out1119, out _out1120);
                r = _out1118;
                resultingOwnership = _out1119;
                readIdents = _out1120;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3764___mcc_h1074 = _source161.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1121;
                DCOMP._IOwnership _out1122;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1123;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1121, out _out1122, out _out1123);
                r = _out1121;
                resultingOwnership = _out1122;
                readIdents = _out1123;
              }
            }
          } else {
            DAST._IType _source163 = _3146___mcc_h1;
            if (_source163.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3765___mcc_h1076 = _source163.dtor_Path_i_a0;
              Dafny.ISequence<DAST._IType> _3766___mcc_h1077 = _source163.dtor_typeArgs;
              DAST._IResolvedType _3767___mcc_h1078 = _source163.dtor_resolved;
              DAST._IResolvedType _source164 = _3767___mcc_h1078;
              if (_source164.is_Datatype) {
                DAST._IDatatypeType _3768___mcc_h1082 = _source164.dtor_datatypeType;
                {
                  RAST._IExpr _out1124;
                  DCOMP._IOwnership _out1125;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1126;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1124, out _out1125, out _out1126);
                  r = _out1124;
                  resultingOwnership = _out1125;
                  readIdents = _out1126;
                }
              } else if (_source164.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3769___mcc_h1084 = _source164.dtor_path;
                Dafny.ISequence<DAST._IAttribute> _3770___mcc_h1085 = _source164.dtor_attributes;
                {
                  RAST._IExpr _out1127;
                  DCOMP._IOwnership _out1128;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1129;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1127, out _out1128, out _out1129);
                  r = _out1127;
                  resultingOwnership = _out1128;
                  readIdents = _out1129;
                }
              } else {
                DAST._IType _3771___mcc_h1088 = _source164.dtor_baseType;
                DAST._INewtypeRange _3772___mcc_h1089 = _source164.dtor_range;
                bool _3773___mcc_h1090 = _source164.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _3774___mcc_h1091 = _source164.dtor_attributes;
                Dafny.ISequence<DAST._IAttribute> _3775_attributes = _3774___mcc_h1091;
                bool _3776_erase = _3773___mcc_h1090;
                DAST._INewtypeRange _3777_range = _3772___mcc_h1089;
                DAST._IType _3778_b = _3771___mcc_h1088;
                {
                  RAST._IExpr _out1130;
                  DCOMP._IOwnership _out1131;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1132;
                  (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1130, out _out1131, out _out1132);
                  r = _out1130;
                  resultingOwnership = _out1131;
                  readIdents = _out1132;
                }
              }
            } else if (_source163.is_Nullable) {
              DAST._IType _3779___mcc_h1096 = _source163.dtor_Nullable_i_a0;
              {
                RAST._IExpr _out1133;
                DCOMP._IOwnership _out1134;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1135;
                (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1133, out _out1134, out _out1135);
                r = _out1133;
                resultingOwnership = _out1134;
                readIdents = _out1135;
              }
            } else if (_source163.is_Tuple) {
              Dafny.ISequence<DAST._IType> _3780___mcc_h1098 = _source163.dtor_Tuple_i_a0;
              {
                RAST._IExpr _out1136;
                DCOMP._IOwnership _out1137;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1138;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1136, out _out1137, out _out1138);
                r = _out1136;
                resultingOwnership = _out1137;
                readIdents = _out1138;
              }
            } else if (_source163.is_Array) {
              DAST._IType _3781___mcc_h1100 = _source163.dtor_element;
              BigInteger _3782___mcc_h1101 = _source163.dtor_dims;
              {
                RAST._IExpr _out1139;
                DCOMP._IOwnership _out1140;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1141;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1139, out _out1140, out _out1141);
                r = _out1139;
                resultingOwnership = _out1140;
                readIdents = _out1141;
              }
            } else if (_source163.is_Seq) {
              DAST._IType _3783___mcc_h1104 = _source163.dtor_element;
              {
                RAST._IExpr _out1142;
                DCOMP._IOwnership _out1143;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1144;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1142, out _out1143, out _out1144);
                r = _out1142;
                resultingOwnership = _out1143;
                readIdents = _out1144;
              }
            } else if (_source163.is_Set) {
              DAST._IType _3784___mcc_h1106 = _source163.dtor_element;
              {
                RAST._IExpr _out1145;
                DCOMP._IOwnership _out1146;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1147;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1145, out _out1146, out _out1147);
                r = _out1145;
                resultingOwnership = _out1146;
                readIdents = _out1147;
              }
            } else if (_source163.is_Multiset) {
              DAST._IType _3785___mcc_h1108 = _source163.dtor_element;
              {
                RAST._IExpr _out1148;
                DCOMP._IOwnership _out1149;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1150;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1148, out _out1149, out _out1150);
                r = _out1148;
                resultingOwnership = _out1149;
                readIdents = _out1150;
              }
            } else if (_source163.is_Map) {
              DAST._IType _3786___mcc_h1110 = _source163.dtor_key;
              DAST._IType _3787___mcc_h1111 = _source163.dtor_value;
              {
                RAST._IExpr _out1151;
                DCOMP._IOwnership _out1152;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1153;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1151, out _out1152, out _out1153);
                r = _out1151;
                resultingOwnership = _out1152;
                readIdents = _out1153;
              }
            } else if (_source163.is_SetBuilder) {
              DAST._IType _3788___mcc_h1114 = _source163.dtor_element;
              {
                RAST._IExpr _out1154;
                DCOMP._IOwnership _out1155;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1156;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1154, out _out1155, out _out1156);
                r = _out1154;
                resultingOwnership = _out1155;
                readIdents = _out1156;
              }
            } else if (_source163.is_MapBuilder) {
              DAST._IType _3789___mcc_h1116 = _source163.dtor_key;
              DAST._IType _3790___mcc_h1117 = _source163.dtor_value;
              {
                RAST._IExpr _out1157;
                DCOMP._IOwnership _out1158;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1159;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1157, out _out1158, out _out1159);
                r = _out1157;
                resultingOwnership = _out1158;
                readIdents = _out1159;
              }
            } else if (_source163.is_Arrow) {
              Dafny.ISequence<DAST._IType> _3791___mcc_h1120 = _source163.dtor_args;
              DAST._IType _3792___mcc_h1121 = _source163.dtor_result;
              {
                RAST._IExpr _out1160;
                DCOMP._IOwnership _out1161;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1162;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1160, out _out1161, out _out1162);
                r = _out1160;
                resultingOwnership = _out1161;
                readIdents = _out1162;
              }
            } else if (_source163.is_Primitive) {
              DAST._IPrimitive _3793___mcc_h1124 = _source163.dtor_Primitive_i_a0;
              DAST._IPrimitive _source165 = _3793___mcc_h1124;
              if (_source165.is_Int) {
                {
                  RAST._IType _3794_rhsType;
                  RAST._IType _out1163;
                  _out1163 = (this).GenType(_3140_fromTpe, true, false);
                  _3794_rhsType = _out1163;
                  RAST._IExpr _3795_recursiveGen;
                  DCOMP._IOwnership _3796___v98;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3797_recIdents;
                  RAST._IExpr _out1164;
                  DCOMP._IOwnership _out1165;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1166;
                  (this).GenExpr(_3139_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1164, out _out1165, out _out1166);
                  _3795_recursiveGen = _out1164;
                  _3796___v98 = _out1165;
                  _3797_recIdents = _out1166;
                  r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_3795_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                  RAST._IExpr _out1167;
                  DCOMP._IOwnership _out1168;
                  DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1167, out _out1168);
                  r = _out1167;
                  resultingOwnership = _out1168;
                  readIdents = _3797_recIdents;
                }
              } else if (_source165.is_Real) {
                {
                  RAST._IExpr _out1169;
                  DCOMP._IOwnership _out1170;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1171;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1169, out _out1170, out _out1171);
                  r = _out1169;
                  resultingOwnership = _out1170;
                  readIdents = _out1171;
                }
              } else if (_source165.is_String) {
                {
                  RAST._IExpr _out1172;
                  DCOMP._IOwnership _out1173;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1174;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1172, out _out1173, out _out1174);
                  r = _out1172;
                  resultingOwnership = _out1173;
                  readIdents = _out1174;
                }
              } else if (_source165.is_Bool) {
                {
                  RAST._IExpr _out1175;
                  DCOMP._IOwnership _out1176;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1177;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1175, out _out1176, out _out1177);
                  r = _out1175;
                  resultingOwnership = _out1176;
                  readIdents = _out1177;
                }
              } else {
                {
                  RAST._IExpr _out1178;
                  DCOMP._IOwnership _out1179;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1180;
                  (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1178, out _out1179, out _out1180);
                  r = _out1178;
                  resultingOwnership = _out1179;
                  readIdents = _out1180;
                }
              }
            } else if (_source163.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _3798___mcc_h1126 = _source163.dtor_Passthrough_i_a0;
              {
                RAST._IExpr _out1181;
                DCOMP._IOwnership _out1182;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1183;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1181, out _out1182, out _out1183);
                r = _out1181;
                resultingOwnership = _out1182;
                readIdents = _out1183;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _3799___mcc_h1128 = _source163.dtor_TypeArg_i_a0;
              {
                RAST._IExpr _out1184;
                DCOMP._IOwnership _out1185;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1186;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1184, out _out1185, out _out1186);
                r = _out1184;
                resultingOwnership = _out1185;
                readIdents = _out1186;
              }
            }
          }
        } else if (_source124.is_Passthrough) {
          Dafny.ISequence<Dafny.Rune> _3800___mcc_h1130 = _source124.dtor_Passthrough_i_a0;
          DAST._IType _source166 = _3146___mcc_h1;
          if (_source166.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3801___mcc_h1134 = _source166.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3802___mcc_h1135 = _source166.dtor_typeArgs;
            DAST._IResolvedType _3803___mcc_h1136 = _source166.dtor_resolved;
            DAST._IResolvedType _source167 = _3803___mcc_h1136;
            if (_source167.is_Datatype) {
              DAST._IDatatypeType _3804___mcc_h1140 = _source167.dtor_datatypeType;
              {
                RAST._IExpr _out1187;
                DCOMP._IOwnership _out1188;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1189;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1187, out _out1188, out _out1189);
                r = _out1187;
                resultingOwnership = _out1188;
                readIdents = _out1189;
              }
            } else if (_source167.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3805___mcc_h1142 = _source167.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3806___mcc_h1143 = _source167.dtor_attributes;
              {
                RAST._IExpr _out1190;
                DCOMP._IOwnership _out1191;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1192;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1190, out _out1191, out _out1192);
                r = _out1190;
                resultingOwnership = _out1191;
                readIdents = _out1192;
              }
            } else {
              DAST._IType _3807___mcc_h1146 = _source167.dtor_baseType;
              DAST._INewtypeRange _3808___mcc_h1147 = _source167.dtor_range;
              bool _3809___mcc_h1148 = _source167.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3810___mcc_h1149 = _source167.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3811_attributes = _3810___mcc_h1149;
              bool _3812_erase = _3809___mcc_h1148;
              DAST._INewtypeRange _3813_range = _3808___mcc_h1147;
              DAST._IType _3814_b = _3807___mcc_h1146;
              {
                RAST._IExpr _out1193;
                DCOMP._IOwnership _out1194;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1195;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1193, out _out1194, out _out1195);
                r = _out1193;
                resultingOwnership = _out1194;
                readIdents = _out1195;
              }
            }
          } else if (_source166.is_Nullable) {
            DAST._IType _3815___mcc_h1154 = _source166.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out1196;
              DCOMP._IOwnership _out1197;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1198;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1196, out _out1197, out _out1198);
              r = _out1196;
              resultingOwnership = _out1197;
              readIdents = _out1198;
            }
          } else if (_source166.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3816___mcc_h1156 = _source166.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out1199;
              DCOMP._IOwnership _out1200;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1201;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1199, out _out1200, out _out1201);
              r = _out1199;
              resultingOwnership = _out1200;
              readIdents = _out1201;
            }
          } else if (_source166.is_Array) {
            DAST._IType _3817___mcc_h1158 = _source166.dtor_element;
            BigInteger _3818___mcc_h1159 = _source166.dtor_dims;
            {
              RAST._IExpr _out1202;
              DCOMP._IOwnership _out1203;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1204;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1202, out _out1203, out _out1204);
              r = _out1202;
              resultingOwnership = _out1203;
              readIdents = _out1204;
            }
          } else if (_source166.is_Seq) {
            DAST._IType _3819___mcc_h1162 = _source166.dtor_element;
            {
              RAST._IExpr _out1205;
              DCOMP._IOwnership _out1206;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1207;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1205, out _out1206, out _out1207);
              r = _out1205;
              resultingOwnership = _out1206;
              readIdents = _out1207;
            }
          } else if (_source166.is_Set) {
            DAST._IType _3820___mcc_h1164 = _source166.dtor_element;
            {
              RAST._IExpr _out1208;
              DCOMP._IOwnership _out1209;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1210;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1208, out _out1209, out _out1210);
              r = _out1208;
              resultingOwnership = _out1209;
              readIdents = _out1210;
            }
          } else if (_source166.is_Multiset) {
            DAST._IType _3821___mcc_h1166 = _source166.dtor_element;
            {
              RAST._IExpr _out1211;
              DCOMP._IOwnership _out1212;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1213;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1211, out _out1212, out _out1213);
              r = _out1211;
              resultingOwnership = _out1212;
              readIdents = _out1213;
            }
          } else if (_source166.is_Map) {
            DAST._IType _3822___mcc_h1168 = _source166.dtor_key;
            DAST._IType _3823___mcc_h1169 = _source166.dtor_value;
            {
              RAST._IExpr _out1214;
              DCOMP._IOwnership _out1215;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1216;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1214, out _out1215, out _out1216);
              r = _out1214;
              resultingOwnership = _out1215;
              readIdents = _out1216;
            }
          } else if (_source166.is_SetBuilder) {
            DAST._IType _3824___mcc_h1172 = _source166.dtor_element;
            {
              RAST._IExpr _out1217;
              DCOMP._IOwnership _out1218;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1219;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1217, out _out1218, out _out1219);
              r = _out1217;
              resultingOwnership = _out1218;
              readIdents = _out1219;
            }
          } else if (_source166.is_MapBuilder) {
            DAST._IType _3825___mcc_h1174 = _source166.dtor_key;
            DAST._IType _3826___mcc_h1175 = _source166.dtor_value;
            {
              RAST._IExpr _out1220;
              DCOMP._IOwnership _out1221;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1222;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1220, out _out1221, out _out1222);
              r = _out1220;
              resultingOwnership = _out1221;
              readIdents = _out1222;
            }
          } else if (_source166.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3827___mcc_h1178 = _source166.dtor_args;
            DAST._IType _3828___mcc_h1179 = _source166.dtor_result;
            {
              RAST._IExpr _out1223;
              DCOMP._IOwnership _out1224;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1225;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1223, out _out1224, out _out1225);
              r = _out1223;
              resultingOwnership = _out1224;
              readIdents = _out1225;
            }
          } else if (_source166.is_Primitive) {
            DAST._IPrimitive _3829___mcc_h1182 = _source166.dtor_Primitive_i_a0;
            DAST._IPrimitive _source168 = _3829___mcc_h1182;
            if (_source168.is_Int) {
              {
                RAST._IType _3830_rhsType;
                RAST._IType _out1226;
                _out1226 = (this).GenType(_3140_fromTpe, true, false);
                _3830_rhsType = _out1226;
                RAST._IExpr _3831_recursiveGen;
                DCOMP._IOwnership _3832___v96;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3833_recIdents;
                RAST._IExpr _out1227;
                DCOMP._IOwnership _out1228;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1229;
                (this).GenExpr(_3139_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1227, out _out1228, out _out1229);
                _3831_recursiveGen = _out1227;
                _3832___v96 = _out1228;
                _3833_recIdents = _out1229;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from("), (_3831_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")}")));
                RAST._IExpr _out1230;
                DCOMP._IOwnership _out1231;
                DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1230, out _out1231);
                r = _out1230;
                resultingOwnership = _out1231;
                readIdents = _3833_recIdents;
              }
            } else if (_source168.is_Real) {
              {
                RAST._IExpr _out1232;
                DCOMP._IOwnership _out1233;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1234;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1232, out _out1233, out _out1234);
                r = _out1232;
                resultingOwnership = _out1233;
                readIdents = _out1234;
              }
            } else if (_source168.is_String) {
              {
                RAST._IExpr _out1235;
                DCOMP._IOwnership _out1236;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1237;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1235, out _out1236, out _out1237);
                r = _out1235;
                resultingOwnership = _out1236;
                readIdents = _out1237;
              }
            } else if (_source168.is_Bool) {
              {
                RAST._IExpr _out1238;
                DCOMP._IOwnership _out1239;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1240;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1238, out _out1239, out _out1240);
                r = _out1238;
                resultingOwnership = _out1239;
                readIdents = _out1240;
              }
            } else {
              {
                RAST._IExpr _out1241;
                DCOMP._IOwnership _out1242;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1243;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1241, out _out1242, out _out1243);
                r = _out1241;
                resultingOwnership = _out1242;
                readIdents = _out1243;
              }
            }
          } else if (_source166.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3834___mcc_h1184 = _source166.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _3835_recursiveGen;
              DCOMP._IOwnership _3836___v101;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3837_recIdents;
              RAST._IExpr _out1244;
              DCOMP._IOwnership _out1245;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1246;
              (this).GenExpr(_3139_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1244, out _out1245, out _out1246);
              _3835_recursiveGen = _out1244;
              _3836___v101 = _out1245;
              _3837_recIdents = _out1246;
              RAST._IType _3838_toTpeGen;
              RAST._IType _out1247;
              _out1247 = (this).GenType(_3141_toTpe, true, false);
              _3838_toTpeGen = _out1247;
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_3835_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_3838_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
              RAST._IExpr _out1248;
              DCOMP._IOwnership _out1249;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1248, out _out1249);
              r = _out1248;
              resultingOwnership = _out1249;
              readIdents = _3837_recIdents;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3839___mcc_h1186 = _source166.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out1250;
              DCOMP._IOwnership _out1251;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1252;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1250, out _out1251, out _out1252);
              r = _out1250;
              resultingOwnership = _out1251;
              readIdents = _out1252;
            }
          }
        } else {
          Dafny.ISequence<Dafny.Rune> _3840___mcc_h1188 = _source124.dtor_TypeArg_i_a0;
          DAST._IType _source169 = _3146___mcc_h1;
          if (_source169.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3841___mcc_h1192 = _source169.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _3842___mcc_h1193 = _source169.dtor_typeArgs;
            DAST._IResolvedType _3843___mcc_h1194 = _source169.dtor_resolved;
            DAST._IResolvedType _source170 = _3843___mcc_h1194;
            if (_source170.is_Datatype) {
              DAST._IDatatypeType _3844___mcc_h1198 = _source170.dtor_datatypeType;
              {
                RAST._IExpr _out1253;
                DCOMP._IOwnership _out1254;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1255;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1253, out _out1254, out _out1255);
                r = _out1253;
                resultingOwnership = _out1254;
                readIdents = _out1255;
              }
            } else if (_source170.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3845___mcc_h1200 = _source170.dtor_path;
              Dafny.ISequence<DAST._IAttribute> _3846___mcc_h1201 = _source170.dtor_attributes;
              {
                RAST._IExpr _out1256;
                DCOMP._IOwnership _out1257;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1258;
                (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1256, out _out1257, out _out1258);
                r = _out1256;
                resultingOwnership = _out1257;
                readIdents = _out1258;
              }
            } else {
              DAST._IType _3847___mcc_h1204 = _source170.dtor_baseType;
              DAST._INewtypeRange _3848___mcc_h1205 = _source170.dtor_range;
              bool _3849___mcc_h1206 = _source170.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _3850___mcc_h1207 = _source170.dtor_attributes;
              Dafny.ISequence<DAST._IAttribute> _3851_attributes = _3850___mcc_h1207;
              bool _3852_erase = _3849___mcc_h1206;
              DAST._INewtypeRange _3853_range = _3848___mcc_h1205;
              DAST._IType _3854_b = _3847___mcc_h1204;
              {
                RAST._IExpr _out1259;
                DCOMP._IOwnership _out1260;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1261;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out1259, out _out1260, out _out1261);
                r = _out1259;
                resultingOwnership = _out1260;
                readIdents = _out1261;
              }
            }
          } else if (_source169.is_Nullable) {
            DAST._IType _3855___mcc_h1212 = _source169.dtor_Nullable_i_a0;
            {
              RAST._IExpr _out1262;
              DCOMP._IOwnership _out1263;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1264;
              (this).GenExprConvertToNullable(e, selfIdent, env, expectedOwnership, out _out1262, out _out1263, out _out1264);
              r = _out1262;
              resultingOwnership = _out1263;
              readIdents = _out1264;
            }
          } else if (_source169.is_Tuple) {
            Dafny.ISequence<DAST._IType> _3856___mcc_h1214 = _source169.dtor_Tuple_i_a0;
            {
              RAST._IExpr _out1265;
              DCOMP._IOwnership _out1266;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1267;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1265, out _out1266, out _out1267);
              r = _out1265;
              resultingOwnership = _out1266;
              readIdents = _out1267;
            }
          } else if (_source169.is_Array) {
            DAST._IType _3857___mcc_h1216 = _source169.dtor_element;
            BigInteger _3858___mcc_h1217 = _source169.dtor_dims;
            {
              RAST._IExpr _out1268;
              DCOMP._IOwnership _out1269;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1270;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1268, out _out1269, out _out1270);
              r = _out1268;
              resultingOwnership = _out1269;
              readIdents = _out1270;
            }
          } else if (_source169.is_Seq) {
            DAST._IType _3859___mcc_h1220 = _source169.dtor_element;
            {
              RAST._IExpr _out1271;
              DCOMP._IOwnership _out1272;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1273;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1271, out _out1272, out _out1273);
              r = _out1271;
              resultingOwnership = _out1272;
              readIdents = _out1273;
            }
          } else if (_source169.is_Set) {
            DAST._IType _3860___mcc_h1222 = _source169.dtor_element;
            {
              RAST._IExpr _out1274;
              DCOMP._IOwnership _out1275;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1276;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1274, out _out1275, out _out1276);
              r = _out1274;
              resultingOwnership = _out1275;
              readIdents = _out1276;
            }
          } else if (_source169.is_Multiset) {
            DAST._IType _3861___mcc_h1224 = _source169.dtor_element;
            {
              RAST._IExpr _out1277;
              DCOMP._IOwnership _out1278;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1279;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1277, out _out1278, out _out1279);
              r = _out1277;
              resultingOwnership = _out1278;
              readIdents = _out1279;
            }
          } else if (_source169.is_Map) {
            DAST._IType _3862___mcc_h1226 = _source169.dtor_key;
            DAST._IType _3863___mcc_h1227 = _source169.dtor_value;
            {
              RAST._IExpr _out1280;
              DCOMP._IOwnership _out1281;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1282;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1280, out _out1281, out _out1282);
              r = _out1280;
              resultingOwnership = _out1281;
              readIdents = _out1282;
            }
          } else if (_source169.is_SetBuilder) {
            DAST._IType _3864___mcc_h1230 = _source169.dtor_element;
            {
              RAST._IExpr _out1283;
              DCOMP._IOwnership _out1284;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1285;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1283, out _out1284, out _out1285);
              r = _out1283;
              resultingOwnership = _out1284;
              readIdents = _out1285;
            }
          } else if (_source169.is_MapBuilder) {
            DAST._IType _3865___mcc_h1232 = _source169.dtor_key;
            DAST._IType _3866___mcc_h1233 = _source169.dtor_value;
            {
              RAST._IExpr _out1286;
              DCOMP._IOwnership _out1287;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1288;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1286, out _out1287, out _out1288);
              r = _out1286;
              resultingOwnership = _out1287;
              readIdents = _out1288;
            }
          } else if (_source169.is_Arrow) {
            Dafny.ISequence<DAST._IType> _3867___mcc_h1236 = _source169.dtor_args;
            DAST._IType _3868___mcc_h1237 = _source169.dtor_result;
            {
              RAST._IExpr _out1289;
              DCOMP._IOwnership _out1290;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1291;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1289, out _out1290, out _out1291);
              r = _out1289;
              resultingOwnership = _out1290;
              readIdents = _out1291;
            }
          } else if (_source169.is_Primitive) {
            DAST._IPrimitive _3869___mcc_h1240 = _source169.dtor_Primitive_i_a0;
            {
              RAST._IExpr _out1292;
              DCOMP._IOwnership _out1293;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1294;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1292, out _out1293, out _out1294);
              r = _out1292;
              resultingOwnership = _out1293;
              readIdents = _out1294;
            }
          } else if (_source169.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _3870___mcc_h1242 = _source169.dtor_Passthrough_i_a0;
            {
              RAST._IExpr _out1295;
              DCOMP._IOwnership _out1296;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1297;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1295, out _out1296, out _out1297);
              r = _out1295;
              resultingOwnership = _out1296;
              readIdents = _out1297;
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _3871___mcc_h1244 = _source169.dtor_TypeArg_i_a0;
            {
              RAST._IExpr _out1298;
              DCOMP._IOwnership _out1299;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1300;
              (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out1298, out _out1299, out _out1300);
              r = _out1298;
              resultingOwnership = _out1299;
              readIdents = _out1300;
            }
          }
        }
      }
      return ;
    }
    public void GenIdent(Dafny.ISequence<Dafny.Rune> rName, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      r = RAST.Expr.create_Identifier(rName);
      Std.Wrappers._IOption<RAST._IType> _3872_tpe;
      _3872_tpe = (env).GetType(rName);
      bool _3873_currentlyBorrowed;
      _3873_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _3874_noNeedOfClone;
      _3874_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        r = RAST.__default.BorrowMut(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        if (!(_3874_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_3874_noNeedOfClone)) {
          r = RAST.__default.Clone(r);
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_3873_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        r = RAST.__default.Borrow(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      }
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(rName);
      return ;
    }
    public void GenExpr(DAST._IExpression e, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source171 = e;
      if (_source171.is_Literal) {
        DAST._ILiteral _3875___mcc_h0 = _source171.dtor_Literal_i_a0;
        RAST._IExpr _out1301;
        DCOMP._IOwnership _out1302;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1303;
        (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out1301, out _out1302, out _out1303);
        r = _out1301;
        resultingOwnership = _out1302;
        readIdents = _out1303;
      } else if (_source171.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _3876___mcc_h1 = _source171.dtor_Ident_i_a0;
        Dafny.ISequence<Dafny.Rune> _3877_name = _3876___mcc_h1;
        {
          RAST._IExpr _out1304;
          DCOMP._IOwnership _out1305;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1306;
          (this).GenIdent(DCOMP.__default.escapeName(_3877_name), selfIdent, env, expectedOwnership, out _out1304, out _out1305, out _out1306);
          r = _out1304;
          resultingOwnership = _out1305;
          readIdents = _out1306;
        }
      } else if (_source171.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3878___mcc_h2 = _source171.dtor_Companion_i_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3879_path = _3878___mcc_h2;
        {
          RAST._IExpr _out1307;
          _out1307 = DCOMP.COMP.GenPathExpr(_3879_path);
          r = _out1307;
          if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
            resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          } else {
            RAST._IExpr _out1308;
            DCOMP._IOwnership _out1309;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1308, out _out1309);
            r = _out1308;
            resultingOwnership = _out1309;
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source171.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _3880___mcc_h3 = _source171.dtor_Tuple_i_a0;
        Dafny.ISequence<DAST._IExpression> _3881_values = _3880___mcc_h3;
        {
          Dafny.ISequence<RAST._IExpr> _3882_exprs;
          _3882_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi30 = new BigInteger((_3881_values).Count);
          for (BigInteger _3883_i = BigInteger.Zero; _3883_i < _hi30; _3883_i++) {
            RAST._IExpr _3884_recursiveGen;
            DCOMP._IOwnership _3885___v104;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3886_recIdents;
            RAST._IExpr _out1310;
            DCOMP._IOwnership _out1311;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1312;
            (this).GenExpr((_3881_values).Select(_3883_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1310, out _out1311, out _out1312);
            _3884_recursiveGen = _out1310;
            _3885___v104 = _out1311;
            _3886_recIdents = _out1312;
            _3882_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_3882_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_3884_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3886_recIdents);
          }
          r = (((new BigInteger((_3881_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_3882_exprs)) : (RAST.__default.SystemTuple(_3882_exprs)));
          RAST._IExpr _out1313;
          DCOMP._IOwnership _out1314;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1313, out _out1314);
          r = _out1313;
          resultingOwnership = _out1314;
          return ;
        }
      } else if (_source171.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3887___mcc_h4 = _source171.dtor_path;
        Dafny.ISequence<DAST._IType> _3888___mcc_h5 = _source171.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _3889___mcc_h6 = _source171.dtor_args;
        Dafny.ISequence<DAST._IExpression> _3890_args = _3889___mcc_h6;
        Dafny.ISequence<DAST._IType> _3891_typeArgs = _3888___mcc_h5;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3892_path = _3887___mcc_h4;
        {
          RAST._IExpr _out1315;
          _out1315 = DCOMP.COMP.GenPathExpr(_3892_path);
          r = _out1315;
          if ((new BigInteger((_3891_typeArgs).Count)).Sign == 1) {
            Dafny.ISequence<RAST._IType> _3893_typeExprs;
            _3893_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi31 = new BigInteger((_3891_typeArgs).Count);
            for (BigInteger _3894_i = BigInteger.Zero; _3894_i < _hi31; _3894_i++) {
              RAST._IType _3895_typeExpr;
              RAST._IType _out1316;
              _out1316 = (this).GenType((_3891_typeArgs).Select(_3894_i), false, false);
              _3895_typeExpr = _out1316;
              _3893_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_3893_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_3895_typeExpr));
            }
            r = (r).ApplyType(_3893_typeExprs);
          }
          r = (r).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_allocated"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IExpr> _3896_arguments;
          _3896_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_3890_args).Count);
          for (BigInteger _3897_i = BigInteger.Zero; _3897_i < _hi32; _3897_i++) {
            RAST._IExpr _3898_recursiveGen;
            DCOMP._IOwnership _3899___v105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3900_recIdents;
            RAST._IExpr _out1317;
            DCOMP._IOwnership _out1318;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1319;
            (this).GenExpr((_3890_args).Select(_3897_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1317, out _out1318, out _out1319);
            _3898_recursiveGen = _out1317;
            _3899___v105 = _out1318;
            _3900_recIdents = _out1319;
            _3896_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3896_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_3898_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3900_recIdents);
          }
          r = (r).Apply(_3896_arguments);
          RAST._IExpr _out1320;
          DCOMP._IOwnership _out1321;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1320, out _out1321);
          r = _out1320;
          resultingOwnership = _out1321;
          return ;
        }
      } else if (_source171.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _3901___mcc_h7 = _source171.dtor_dims;
        DAST._IType _3902___mcc_h8 = _source171.dtor_typ;
        DAST._IType _3903_typ = _3902___mcc_h8;
        Dafny.ISequence<DAST._IExpression> _3904_dims = _3901___mcc_h7;
        {
          BigInteger _3905_i;
          _3905_i = (new BigInteger((_3904_dims).Count)) - (BigInteger.One);
          RAST._IType _3906_genTyp;
          RAST._IType _out1322;
          _out1322 = (this).GenType(_3903_typ, false, false);
          _3906_genTyp = _out1322;
          Dafny.ISequence<Dafny.Rune> _3907_s;
          _3907_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_3906_genTyp)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::std::default::Default>::default()"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_3905_i).Sign != -1) {
            RAST._IExpr _3908_recursiveGen;
            DCOMP._IOwnership _3909___v106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3910_recIdents;
            RAST._IExpr _out1323;
            DCOMP._IOwnership _out1324;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1325;
            (this).GenExpr((_3904_dims).Select(_3905_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1323, out _out1324, out _out1325);
            _3908_recursiveGen = _out1323;
            _3909___v106 = _out1324;
            _3910_recIdents = _out1325;
            _3907_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), _3907_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), (_3908_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3910_recIdents);
            _3905_i = (_3905_i) - (BigInteger.One);
          }
          r = RAST.Expr.create_RawExpr(_3907_s);
          RAST._IExpr _out1326;
          DCOMP._IOwnership _out1327;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1326, out _out1327);
          r = _out1326;
          resultingOwnership = _out1327;
          return ;
        }
      } else if (_source171.is_DatatypeValue) {
        DAST._IDatatypeType _3911___mcc_h9 = _source171.dtor_datatypeType;
        Dafny.ISequence<DAST._IType> _3912___mcc_h10 = _source171.dtor_typeArgs;
        Dafny.ISequence<Dafny.Rune> _3913___mcc_h11 = _source171.dtor_variant;
        bool _3914___mcc_h12 = _source171.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3915___mcc_h13 = _source171.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _3916_values = _3915___mcc_h13;
        bool _3917_isCo = _3914___mcc_h12;
        Dafny.ISequence<Dafny.Rune> _3918_variant = _3913___mcc_h11;
        Dafny.ISequence<DAST._IType> _3919_typeArgs = _3912___mcc_h10;
        DAST._IDatatypeType _3920_datatypeType = _3911___mcc_h9;
        {
          RAST._IExpr _out1328;
          _out1328 = DCOMP.COMP.GenPathExpr((_3920_datatypeType).dtor_path);
          r = _out1328;
          Dafny.ISequence<RAST._IType> _3921_genTypeArgs;
          _3921_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
          BigInteger _hi33 = new BigInteger((_3919_typeArgs).Count);
          for (BigInteger _3922_i = BigInteger.Zero; _3922_i < _hi33; _3922_i++) {
            RAST._IType _3923_typeExpr;
            RAST._IType _out1329;
            _out1329 = (this).GenType((_3919_typeArgs).Select(_3922_i), false, false);
            _3923_typeExpr = _out1329;
            _3921_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_3921_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_3923_typeExpr));
          }
          if ((new BigInteger((_3919_typeArgs).Count)).Sign == 1) {
            r = (r).ApplyType(_3921_genTypeArgs);
          }
          r = (r).MSel(DCOMP.__default.escapeName(_3918_variant));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IAssignIdentifier> _3924_assignments;
          _3924_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
          BigInteger _hi34 = new BigInteger((_3916_values).Count);
          for (BigInteger _3925_i = BigInteger.Zero; _3925_i < _hi34; _3925_i++) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs63 = (_3916_values).Select(_3925_i);
            Dafny.ISequence<Dafny.Rune> _3926_name = _let_tmp_rhs63.dtor__0;
            DAST._IExpression _3927_value = _let_tmp_rhs63.dtor__1;
            if (_3917_isCo) {
              RAST._IExpr _3928_recursiveGen;
              DCOMP._IOwnership _3929___v107;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3930_recIdents;
              RAST._IExpr _out1330;
              DCOMP._IOwnership _out1331;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1332;
              (this).GenExpr(_3927_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out1330, out _out1331, out _out1332);
              _3928_recursiveGen = _out1330;
              _3929___v107 = _out1331;
              _3930_recIdents = _out1332;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3930_recIdents);
              Dafny.ISequence<Dafny.Rune> _3931_allReadCloned;
              _3931_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_3930_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _3932_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_3930_recIdents).Elements) {
                  _3932_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                  if ((_3930_recIdents).Contains(_3932_next)) {
                    goto after__ASSIGN_SUCH_THAT_2;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 3163)");
              after__ASSIGN_SUCH_THAT_2: ;
                _3931_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_3931_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _3932_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _3932_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _3930_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_3930_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_3932_next));
              }
              Dafny.ISequence<Dafny.Rune> _3933_wasAssigned;
              _3933_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _3931_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_3928_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
              _3924_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_3924_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_3926_name, RAST.Expr.create_RawExpr(_3933_wasAssigned))));
            } else {
              RAST._IExpr _3934_recursiveGen;
              DCOMP._IOwnership _3935___v108;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3936_recIdents;
              RAST._IExpr _out1333;
              DCOMP._IOwnership _out1334;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1335;
              (this).GenExpr(_3927_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1333, out _out1334, out _out1335);
              _3934_recursiveGen = _out1333;
              _3935___v108 = _out1334;
              _3936_recIdents = _out1335;
              _3924_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_3924_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_3926_name, _3934_recursiveGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3936_recIdents);
            }
          }
          r = RAST.Expr.create_StructBuild(r, _3924_assignments);
          r = RAST.__default.RcNew(r);
          RAST._IExpr _out1336;
          DCOMP._IOwnership _out1337;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1336, out _out1337);
          r = _out1336;
          resultingOwnership = _out1337;
          return ;
        }
      } else if (_source171.is_Convert) {
        DAST._IExpression _3937___mcc_h14 = _source171.dtor_value;
        DAST._IType _3938___mcc_h15 = _source171.dtor_from;
        DAST._IType _3939___mcc_h16 = _source171.dtor_typ;
        {
          RAST._IExpr _out1338;
          DCOMP._IOwnership _out1339;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1340;
          (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out1338, out _out1339, out _out1340);
          r = _out1338;
          resultingOwnership = _out1339;
          readIdents = _out1340;
        }
      } else if (_source171.is_SeqConstruct) {
        DAST._IExpression _3940___mcc_h17 = _source171.dtor_length;
        DAST._IExpression _3941___mcc_h18 = _source171.dtor_elem;
        DAST._IExpression _3942_expr = _3941___mcc_h18;
        DAST._IExpression _3943_length = _3940___mcc_h17;
        {
          RAST._IExpr _3944_recursiveGen;
          DCOMP._IOwnership _3945___v112;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3946_recIdents;
          RAST._IExpr _out1341;
          DCOMP._IOwnership _out1342;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1343;
          (this).GenExpr(_3942_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1341, out _out1342, out _out1343);
          _3944_recursiveGen = _out1341;
          _3945___v112 = _out1342;
          _3946_recIdents = _out1343;
          RAST._IExpr _3947_lengthGen;
          DCOMP._IOwnership _3948___v113;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3949_lengthIdents;
          RAST._IExpr _out1344;
          DCOMP._IOwnership _out1345;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1346;
          (this).GenExpr(_3943_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1344, out _out1345, out _out1346);
          _3947_lengthGen = _out1344;
          _3948___v113 = _out1345;
          _3949_lengthIdents = _out1346;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_3944_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_3947_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_3946_recIdents, _3949_lengthIdents);
          RAST._IExpr _out1347;
          DCOMP._IOwnership _out1348;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1347, out _out1348);
          r = _out1347;
          resultingOwnership = _out1348;
          return ;
        }
      } else if (_source171.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _3950___mcc_h19 = _source171.dtor_elements;
        DAST._IType _3951___mcc_h20 = _source171.dtor_typ;
        DAST._IType _3952_typ = _3951___mcc_h20;
        Dafny.ISequence<DAST._IExpression> _3953_exprs = _3950___mcc_h19;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IType _3954_genTpe;
          RAST._IType _out1349;
          _out1349 = (this).GenType(_3952_typ, false, false);
          _3954_genTpe = _out1349;
          BigInteger _3955_i;
          _3955_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _3956_args;
          _3956_args = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_3955_i) < (new BigInteger((_3953_exprs).Count))) {
            RAST._IExpr _3957_recursiveGen;
            DCOMP._IOwnership _3958___v114;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3959_recIdents;
            RAST._IExpr _out1350;
            DCOMP._IOwnership _out1351;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1352;
            (this).GenExpr((_3953_exprs).Select(_3955_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1350, out _out1351, out _out1352);
            _3957_recursiveGen = _out1350;
            _3958___v114 = _out1351;
            _3959_recIdents = _out1352;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3959_recIdents);
            _3956_args = Dafny.Sequence<RAST._IExpr>.Concat(_3956_args, Dafny.Sequence<RAST._IExpr>.FromElements(_3957_recursiveGen));
            _3955_i = (_3955_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_3956_args);
          if ((new BigInteger((_3956_args).Count)).Sign == 0) {
            r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_3954_genTpe));
          }
          RAST._IExpr _out1353;
          DCOMP._IOwnership _out1354;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1353, out _out1354);
          r = _out1353;
          resultingOwnership = _out1354;
          return ;
        }
      } else if (_source171.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _3960___mcc_h21 = _source171.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _3961_exprs = _3960___mcc_h21;
        {
          Dafny.ISequence<RAST._IExpr> _3962_generatedValues;
          _3962_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3963_i;
          _3963_i = BigInteger.Zero;
          while ((_3963_i) < (new BigInteger((_3961_exprs).Count))) {
            RAST._IExpr _3964_recursiveGen;
            DCOMP._IOwnership _3965___v115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3966_recIdents;
            RAST._IExpr _out1355;
            DCOMP._IOwnership _out1356;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1357;
            (this).GenExpr((_3961_exprs).Select(_3963_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1355, out _out1356, out _out1357);
            _3964_recursiveGen = _out1355;
            _3965___v115 = _out1356;
            _3966_recIdents = _out1357;
            _3962_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_3962_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_3964_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3966_recIdents);
            _3963_i = (_3963_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_3962_generatedValues);
          RAST._IExpr _out1358;
          DCOMP._IOwnership _out1359;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1358, out _out1359);
          r = _out1358;
          resultingOwnership = _out1359;
          return ;
        }
      } else if (_source171.is_MultisetValue) {
        Dafny.ISequence<DAST._IExpression> _3967___mcc_h22 = _source171.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _3968_exprs = _3967___mcc_h22;
        {
          Dafny.ISequence<RAST._IExpr> _3969_generatedValues;
          _3969_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3970_i;
          _3970_i = BigInteger.Zero;
          while ((_3970_i) < (new BigInteger((_3968_exprs).Count))) {
            RAST._IExpr _3971_recursiveGen;
            DCOMP._IOwnership _3972___v116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3973_recIdents;
            RAST._IExpr _out1360;
            DCOMP._IOwnership _out1361;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1362;
            (this).GenExpr((_3968_exprs).Select(_3970_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1360, out _out1361, out _out1362);
            _3971_recursiveGen = _out1360;
            _3972___v116 = _out1361;
            _3973_recIdents = _out1362;
            _3969_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_3969_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_3971_recursiveGen));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3973_recIdents);
            _3970_i = (_3970_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_3969_generatedValues);
          RAST._IExpr _out1363;
          DCOMP._IOwnership _out1364;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1363, out _out1364);
          r = _out1363;
          resultingOwnership = _out1364;
          return ;
        }
      } else if (_source171.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3974___mcc_h23 = _source171.dtor_mapElems;
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _3975_mapElems = _3974___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _3976_generatedValues;
          _3976_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _3977_i;
          _3977_i = BigInteger.Zero;
          while ((_3977_i) < (new BigInteger((_3975_mapElems).Count))) {
            RAST._IExpr _3978_recursiveGenKey;
            DCOMP._IOwnership _3979___v118;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3980_recIdentsKey;
            RAST._IExpr _out1365;
            DCOMP._IOwnership _out1366;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1367;
            (this).GenExpr(((_3975_mapElems).Select(_3977_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1365, out _out1366, out _out1367);
            _3978_recursiveGenKey = _out1365;
            _3979___v118 = _out1366;
            _3980_recIdentsKey = _out1367;
            RAST._IExpr _3981_recursiveGenValue;
            DCOMP._IOwnership _3982___v119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _3983_recIdentsValue;
            RAST._IExpr _out1368;
            DCOMP._IOwnership _out1369;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1370;
            (this).GenExpr(((_3975_mapElems).Select(_3977_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1368, out _out1369, out _out1370);
            _3981_recursiveGenValue = _out1368;
            _3982___v119 = _out1369;
            _3983_recIdentsValue = _out1370;
            _3976_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_3976_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_3978_recursiveGenKey, _3981_recursiveGenValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _3980_recIdentsKey), _3983_recIdentsValue);
            _3977_i = (_3977_i) + (BigInteger.One);
          }
          _3977_i = BigInteger.Zero;
          Dafny.ISequence<RAST._IExpr> _3984_arguments;
          _3984_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          while ((_3977_i) < (new BigInteger((_3976_generatedValues).Count))) {
            RAST._IExpr _3985_genKey;
            _3985_genKey = ((_3976_generatedValues).Select(_3977_i)).dtor__0;
            RAST._IExpr _3986_genValue;
            _3986_genValue = ((_3976_generatedValues).Select(_3977_i)).dtor__1;
            _3984_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_3984_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _3985_genKey, _3986_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
            _3977_i = (_3977_i) + (BigInteger.One);
          }
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_3984_arguments);
          RAST._IExpr _out1371;
          DCOMP._IOwnership _out1372;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1371, out _out1372);
          r = _out1371;
          resultingOwnership = _out1372;
          return ;
        }
      } else if (_source171.is_MapBuilder) {
        DAST._IType _3987___mcc_h24 = _source171.dtor_keyType;
        DAST._IType _3988___mcc_h25 = _source171.dtor_valueType;
        DAST._IType _3989_valueType = _3988___mcc_h25;
        DAST._IType _3990_keyType = _3987___mcc_h24;
        {
          RAST._IType _3991_kType;
          RAST._IType _out1373;
          _out1373 = (this).GenType(_3990_keyType, false, false);
          _3991_kType = _out1373;
          RAST._IType _3992_vType;
          RAST._IType _out1374;
          _out1374 = (this).GenType(_3989_valueType, false, false);
          _3992_vType = _out1374;
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_3991_kType, _3992_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1375;
          DCOMP._IOwnership _out1376;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1375, out _out1376);
          r = _out1375;
          resultingOwnership = _out1376;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source171.is_SeqUpdate) {
        DAST._IExpression _3993___mcc_h26 = _source171.dtor_expr;
        DAST._IExpression _3994___mcc_h27 = _source171.dtor_indexExpr;
        DAST._IExpression _3995___mcc_h28 = _source171.dtor_value;
        DAST._IExpression _3996_value = _3995___mcc_h28;
        DAST._IExpression _3997_index = _3994___mcc_h27;
        DAST._IExpression _3998_expr = _3993___mcc_h26;
        {
          RAST._IExpr _3999_exprR;
          DCOMP._IOwnership _4000___v120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4001_exprIdents;
          RAST._IExpr _out1377;
          DCOMP._IOwnership _out1378;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1379;
          (this).GenExpr(_3998_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1377, out _out1378, out _out1379);
          _3999_exprR = _out1377;
          _4000___v120 = _out1378;
          _4001_exprIdents = _out1379;
          RAST._IExpr _4002_indexR;
          DCOMP._IOwnership _4003_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4004_indexIdents;
          RAST._IExpr _out1380;
          DCOMP._IOwnership _out1381;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1382;
          (this).GenExpr(_3997_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1380, out _out1381, out _out1382);
          _4002_indexR = _out1380;
          _4003_indexOwnership = _out1381;
          _4004_indexIdents = _out1382;
          RAST._IExpr _4005_valueR;
          DCOMP._IOwnership _4006_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4007_valueIdents;
          RAST._IExpr _out1383;
          DCOMP._IOwnership _out1384;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1385;
          (this).GenExpr(_3996_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1383, out _out1384, out _out1385);
          _4005_valueR = _out1383;
          _4006_valueOwnership = _out1384;
          _4007_valueIdents = _out1385;
          r = ((_3999_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_4002_indexR, _4005_valueR));
          RAST._IExpr _out1386;
          DCOMP._IOwnership _out1387;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1386, out _out1387);
          r = _out1386;
          resultingOwnership = _out1387;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4001_exprIdents, _4004_indexIdents), _4007_valueIdents);
          return ;
        }
      } else if (_source171.is_MapUpdate) {
        DAST._IExpression _4008___mcc_h29 = _source171.dtor_expr;
        DAST._IExpression _4009___mcc_h30 = _source171.dtor_indexExpr;
        DAST._IExpression _4010___mcc_h31 = _source171.dtor_value;
        DAST._IExpression _4011_value = _4010___mcc_h31;
        DAST._IExpression _4012_index = _4009___mcc_h30;
        DAST._IExpression _4013_expr = _4008___mcc_h29;
        {
          RAST._IExpr _4014_exprR;
          DCOMP._IOwnership _4015___v121;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4016_exprIdents;
          RAST._IExpr _out1388;
          DCOMP._IOwnership _out1389;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1390;
          (this).GenExpr(_4013_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1388, out _out1389, out _out1390);
          _4014_exprR = _out1388;
          _4015___v121 = _out1389;
          _4016_exprIdents = _out1390;
          RAST._IExpr _4017_indexR;
          DCOMP._IOwnership _4018_indexOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4019_indexIdents;
          RAST._IExpr _out1391;
          DCOMP._IOwnership _out1392;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1393;
          (this).GenExpr(_4012_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1391, out _out1392, out _out1393);
          _4017_indexR = _out1391;
          _4018_indexOwnership = _out1392;
          _4019_indexIdents = _out1393;
          RAST._IExpr _4020_valueR;
          DCOMP._IOwnership _4021_valueOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4022_valueIdents;
          RAST._IExpr _out1394;
          DCOMP._IOwnership _out1395;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1396;
          (this).GenExpr(_4011_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1394, out _out1395, out _out1396);
          _4020_valueR = _out1394;
          _4021_valueOwnership = _out1395;
          _4022_valueIdents = _out1396;
          r = ((_4014_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_4017_indexR, _4020_valueR));
          RAST._IExpr _out1397;
          DCOMP._IOwnership _out1398;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1397, out _out1398);
          r = _out1397;
          resultingOwnership = _out1398;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4016_exprIdents, _4019_indexIdents), _4022_valueIdents);
          return ;
        }
      } else if (_source171.is_SetBuilder) {
        DAST._IType _4023___mcc_h32 = _source171.dtor_elemType;
        DAST._IType _4024_elemType = _4023___mcc_h32;
        {
          RAST._IType _4025_eType;
          RAST._IType _out1399;
          _out1399 = (this).GenType(_4024_elemType, false, false);
          _4025_eType = _out1399;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_4025_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1400;
          DCOMP._IOwnership _out1401;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1400, out _out1401);
          r = _out1400;
          resultingOwnership = _out1401;
          return ;
        }
      } else if (_source171.is_ToMultiset) {
        DAST._IExpression _4026___mcc_h33 = _source171.dtor_ToMultiset_i_a0;
        DAST._IExpression _4027_expr = _4026___mcc_h33;
        {
          RAST._IExpr _4028_recursiveGen;
          DCOMP._IOwnership _4029___v117;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4030_recIdents;
          RAST._IExpr _out1402;
          DCOMP._IOwnership _out1403;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1404;
          (this).GenExpr(_4027_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1402, out _out1403, out _out1404);
          _4028_recursiveGen = _out1402;
          _4029___v117 = _out1403;
          _4030_recIdents = _out1404;
          r = ((_4028_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          readIdents = _4030_recIdents;
          RAST._IExpr _out1405;
          DCOMP._IOwnership _out1406;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1405, out _out1406);
          r = _out1405;
          resultingOwnership = _out1406;
          return ;
        }
      } else if (_source171.is_This) {
        {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source172 = selfIdent;
          if (_source172.is_None) {
            {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
              RAST._IExpr _out1407;
              DCOMP._IOwnership _out1408;
              DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1407, out _out1408);
              r = _out1407;
              resultingOwnership = _out1408;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
          } else {
            Dafny.ISequence<Dafny.Rune> _4031___mcc_h279 = _source172.dtor_value;
            Dafny.ISequence<Dafny.Rune> _4032_id = _4031___mcc_h279;
            {
              r = RAST.Expr.create_Identifier(_4032_id);
              if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
                r = RAST.__default.Clone(r);
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
                r = RAST.__default.BoxNew(RAST.__default.Clone(r));
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
              } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
                if (!(_4032_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.Borrow(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
              } else {
                if (!(_4032_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  r = RAST.__default.BorrowMut(r);
                }
                resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4032_id);
            }
          }
          return ;
        }
      } else if (_source171.is_Ite) {
        DAST._IExpression _4033___mcc_h34 = _source171.dtor_cond;
        DAST._IExpression _4034___mcc_h35 = _source171.dtor_thn;
        DAST._IExpression _4035___mcc_h36 = _source171.dtor_els;
        DAST._IExpression _4036_f = _4035___mcc_h36;
        DAST._IExpression _4037_t = _4034___mcc_h35;
        DAST._IExpression _4038_cond = _4033___mcc_h34;
        {
          RAST._IExpr _4039_cond;
          DCOMP._IOwnership _4040___v122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4041_recIdentsCond;
          RAST._IExpr _out1409;
          DCOMP._IOwnership _out1410;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1411;
          (this).GenExpr(_4038_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1409, out _out1410, out _out1411);
          _4039_cond = _out1409;
          _4040___v122 = _out1410;
          _4041_recIdentsCond = _out1411;
          Dafny.ISequence<Dafny.Rune> _4042_condString;
          _4042_condString = (_4039_cond)._ToString(DCOMP.__default.IND);
          RAST._IExpr _4043___v123;
          DCOMP._IOwnership _4044_tHasToBeOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4045___v124;
          RAST._IExpr _out1412;
          DCOMP._IOwnership _out1413;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1414;
          (this).GenExpr(_4037_t, selfIdent, env, expectedOwnership, out _out1412, out _out1413, out _out1414);
          _4043___v123 = _out1412;
          _4044_tHasToBeOwned = _out1413;
          _4045___v124 = _out1414;
          RAST._IExpr _4046_fExpr;
          DCOMP._IOwnership _4047_fOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4048_recIdentsF;
          RAST._IExpr _out1415;
          DCOMP._IOwnership _out1416;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1417;
          (this).GenExpr(_4036_f, selfIdent, env, _4044_tHasToBeOwned, out _out1415, out _out1416, out _out1417);
          _4046_fExpr = _out1415;
          _4047_fOwned = _out1416;
          _4048_recIdentsF = _out1417;
          Dafny.ISequence<Dafny.Rune> _4049_fString;
          _4049_fString = (_4046_fExpr)._ToString(DCOMP.__default.IND);
          RAST._IExpr _4050_tExpr;
          DCOMP._IOwnership _4051___v125;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4052_recIdentsT;
          RAST._IExpr _out1418;
          DCOMP._IOwnership _out1419;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1420;
          (this).GenExpr(_4037_t, selfIdent, env, _4047_fOwned, out _out1418, out _out1419, out _out1420);
          _4050_tExpr = _out1418;
          _4051___v125 = _out1419;
          _4052_recIdentsT = _out1420;
          Dafny.ISequence<Dafny.Rune> _4053_tString;
          _4053_tString = (_4050_tExpr)._ToString(DCOMP.__default.IND);
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _4042_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _4053_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _4049_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})")));
          RAST._IExpr _out1421;
          DCOMP._IOwnership _out1422;
          DCOMP.COMP.FromOwnership(r, _4047_fOwned, expectedOwnership, out _out1421, out _out1422);
          r = _out1421;
          resultingOwnership = _out1422;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4041_recIdentsCond, _4052_recIdentsT), _4048_recIdentsF);
          return ;
        }
      } else if (_source171.is_UnOp) {
        DAST._IUnaryOp _4054___mcc_h37 = _source171.dtor_unOp;
        DAST._IExpression _4055___mcc_h38 = _source171.dtor_expr;
        DAST.Format._IUnaryOpFormat _4056___mcc_h39 = _source171.dtor_format1;
        DAST._IUnaryOp _source173 = _4054___mcc_h37;
        if (_source173.is_Not) {
          DAST.Format._IUnaryOpFormat _4057_format = _4056___mcc_h39;
          DAST._IExpression _4058_e = _4055___mcc_h38;
          {
            RAST._IExpr _4059_recursiveGen;
            DCOMP._IOwnership _4060___v126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4061_recIdents;
            RAST._IExpr _out1423;
            DCOMP._IOwnership _out1424;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1425;
            (this).GenExpr(_4058_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1423, out _out1424, out _out1425);
            _4059_recursiveGen = _out1423;
            _4060___v126 = _out1424;
            _4061_recIdents = _out1425;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _4059_recursiveGen, _4057_format);
            RAST._IExpr _out1426;
            DCOMP._IOwnership _out1427;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1426, out _out1427);
            r = _out1426;
            resultingOwnership = _out1427;
            readIdents = _4061_recIdents;
            return ;
          }
        } else if (_source173.is_BitwiseNot) {
          DAST.Format._IUnaryOpFormat _4062_format = _4056___mcc_h39;
          DAST._IExpression _4063_e = _4055___mcc_h38;
          {
            RAST._IExpr _4064_recursiveGen;
            DCOMP._IOwnership _4065___v127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4066_recIdents;
            RAST._IExpr _out1428;
            DCOMP._IOwnership _out1429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1430;
            (this).GenExpr(_4063_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1428, out _out1429, out _out1430);
            _4064_recursiveGen = _out1428;
            _4065___v127 = _out1429;
            _4066_recIdents = _out1430;
            r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _4064_recursiveGen, _4062_format);
            RAST._IExpr _out1431;
            DCOMP._IOwnership _out1432;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1431, out _out1432);
            r = _out1431;
            resultingOwnership = _out1432;
            readIdents = _4066_recIdents;
            return ;
          }
        } else {
          DAST.Format._IUnaryOpFormat _4067_format = _4056___mcc_h39;
          DAST._IExpression _4068_e = _4055___mcc_h38;
          {
            RAST._IExpr _4069_recursiveGen;
            DCOMP._IOwnership _4070_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4071_recIdents;
            RAST._IExpr _out1433;
            DCOMP._IOwnership _out1434;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1435;
            (this).GenExpr(_4068_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1433, out _out1434, out _out1435);
            _4069_recursiveGen = _out1433;
            _4070_recOwned = _out1434;
            _4071_recIdents = _out1435;
            r = ((_4069_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1436;
            DCOMP._IOwnership _out1437;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1436, out _out1437);
            r = _out1436;
            resultingOwnership = _out1437;
            readIdents = _4071_recIdents;
            return ;
          }
        }
      } else if (_source171.is_BinOp) {
        DAST._IBinOp _4072___mcc_h40 = _source171.dtor_op;
        DAST._IExpression _4073___mcc_h41 = _source171.dtor_left;
        DAST._IExpression _4074___mcc_h42 = _source171.dtor_right;
        DAST.Format._IBinaryOpFormat _4075___mcc_h43 = _source171.dtor_format2;
        RAST._IExpr _out1438;
        DCOMP._IOwnership _out1439;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1440;
        (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out1438, out _out1439, out _out1440);
        r = _out1438;
        resultingOwnership = _out1439;
        readIdents = _out1440;
      } else if (_source171.is_ArrayLen) {
        DAST._IExpression _4076___mcc_h44 = _source171.dtor_expr;
        BigInteger _4077___mcc_h45 = _source171.dtor_dim;
        BigInteger _4078_dim = _4077___mcc_h45;
        DAST._IExpression _4079_expr = _4076___mcc_h44;
        {
          RAST._IExpr _4080_recursiveGen;
          DCOMP._IOwnership _4081___v132;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4082_recIdents;
          RAST._IExpr _out1441;
          DCOMP._IOwnership _out1442;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1443;
          (this).GenExpr(_4079_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1441, out _out1442, out _out1443);
          _4080_recursiveGen = _out1441;
          _4081___v132 = _out1442;
          _4082_recIdents = _out1443;
          if ((_4078_dim).Sign == 0) {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), (_4080_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())")));
          } else {
            Dafny.ISequence<Dafny.Rune> _4083_s;
            _4083_s = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(m.borrow().len())")))._ToString(DCOMP.__default.IND);
            BigInteger _4084_i;
            _4084_i = BigInteger.One;
            while ((_4084_i) < (_4078_dim)) {
              _4083_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("m.borrow().get(0).map(|m| "), _4083_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"));
              _4084_i = (_4084_i) + (BigInteger.One);
            }
            r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), (_4080_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow().get(0).map(|m| ")), _4083_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap_or(::dafny_runtime::BigInt::from(0))"))));
          }
          RAST._IExpr _out1444;
          DCOMP._IOwnership _out1445;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1444, out _out1445);
          r = _out1444;
          resultingOwnership = _out1445;
          readIdents = _4082_recIdents;
          return ;
        }
      } else if (_source171.is_MapKeys) {
        DAST._IExpression _4085___mcc_h46 = _source171.dtor_expr;
        DAST._IExpression _4086_expr = _4085___mcc_h46;
        {
          RAST._IExpr _4087_recursiveGen;
          DCOMP._IOwnership _4088___v133;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4089_recIdents;
          RAST._IExpr _out1446;
          DCOMP._IOwnership _out1447;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1448;
          (this).GenExpr(_4086_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1446, out _out1447, out _out1448);
          _4087_recursiveGen = _out1446;
          _4088___v133 = _out1447;
          _4089_recIdents = _out1448;
          readIdents = _4089_recIdents;
          r = ((_4087_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1449;
          DCOMP._IOwnership _out1450;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1449, out _out1450);
          r = _out1449;
          resultingOwnership = _out1450;
          return ;
        }
      } else if (_source171.is_MapValues) {
        DAST._IExpression _4090___mcc_h47 = _source171.dtor_expr;
        DAST._IExpression _4091_expr = _4090___mcc_h47;
        {
          RAST._IExpr _4092_recursiveGen;
          DCOMP._IOwnership _4093___v134;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4094_recIdents;
          RAST._IExpr _out1451;
          DCOMP._IOwnership _out1452;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1453;
          (this).GenExpr(_4091_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1451, out _out1452, out _out1453);
          _4092_recursiveGen = _out1451;
          _4093___v134 = _out1452;
          _4094_recIdents = _out1453;
          readIdents = _4094_recIdents;
          r = ((_4092_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1454;
          DCOMP._IOwnership _out1455;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1454, out _out1455);
          r = _out1454;
          resultingOwnership = _out1455;
          return ;
        }
      } else if (_source171.is_Select) {
        DAST._IExpression _4095___mcc_h48 = _source171.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _4096___mcc_h49 = _source171.dtor_field;
        bool _4097___mcc_h50 = _source171.dtor_isConstant;
        bool _4098___mcc_h51 = _source171.dtor_onDatatype;
        DAST._IType _4099___mcc_h52 = _source171.dtor_fieldType;
        DAST._IExpression _source174 = _4095___mcc_h48;
        if (_source174.is_Literal) {
          DAST._ILiteral _4100___mcc_h53 = _source174.dtor_Literal_i_a0;
          DAST._IType _4101_fieldType = _4099___mcc_h52;
          bool _4102_isDatatype = _4098___mcc_h51;
          bool _4103_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4104_field = _4096___mcc_h49;
          DAST._IExpression _4105_on = _4095___mcc_h48;
          {
            if (_4102_isDatatype) {
              RAST._IExpr _4106_onExpr;
              DCOMP._IOwnership _4107_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4108_recIdents;
              RAST._IExpr _out1456;
              DCOMP._IOwnership _out1457;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1458;
              (this).GenExpr(_4105_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1456, out _out1457, out _out1458);
              _4106_onExpr = _out1456;
              _4107_onOwned = _out1457;
              _4108_recIdents = _out1458;
              r = ((_4106_onExpr).Sel(DCOMP.__default.escapeName(_4104_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4109_typ;
              RAST._IType _out1459;
              _out1459 = (this).GenType(_4101_fieldType, false, false);
              _4109_typ = _out1459;
              if (((_4109_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1460;
                DCOMP._IOwnership _out1461;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1460, out _out1461);
                r = _out1460;
                resultingOwnership = _out1461;
              }
              readIdents = _4108_recIdents;
            } else {
              RAST._IExpr _4110_onExpr;
              DCOMP._IOwnership _4111_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4112_recIdents;
              RAST._IExpr _out1462;
              DCOMP._IOwnership _out1463;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1464;
              (this).GenExpr(_4105_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1462, out _out1463, out _out1464);
              _4110_onExpr = _out1462;
              _4111_onOwned = _out1463;
              _4112_recIdents = _out1464;
              r = _4110_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4104_field));
              if (_4103_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4113_s;
                _4113_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4110_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4104_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4113_s);
              }
              DCOMP._IOwnership _4114_fromOwnership;
              _4114_fromOwnership = ((_4103_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1465;
              DCOMP._IOwnership _out1466;
              DCOMP.COMP.FromOwnership(r, _4114_fromOwnership, expectedOwnership, out _out1465, out _out1466);
              r = _out1465;
              resultingOwnership = _out1466;
              readIdents = _4112_recIdents;
            }
            return ;
          }
        } else if (_source174.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _4115___mcc_h55 = _source174.dtor_Ident_i_a0;
          DAST._IType _4116_fieldType = _4099___mcc_h52;
          bool _4117_isDatatype = _4098___mcc_h51;
          bool _4118_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4119_field = _4096___mcc_h49;
          DAST._IExpression _4120_on = _4095___mcc_h48;
          {
            if (_4117_isDatatype) {
              RAST._IExpr _4121_onExpr;
              DCOMP._IOwnership _4122_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4123_recIdents;
              RAST._IExpr _out1467;
              DCOMP._IOwnership _out1468;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1469;
              (this).GenExpr(_4120_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1467, out _out1468, out _out1469);
              _4121_onExpr = _out1467;
              _4122_onOwned = _out1468;
              _4123_recIdents = _out1469;
              r = ((_4121_onExpr).Sel(DCOMP.__default.escapeName(_4119_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4124_typ;
              RAST._IType _out1470;
              _out1470 = (this).GenType(_4116_fieldType, false, false);
              _4124_typ = _out1470;
              if (((_4124_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1471;
                DCOMP._IOwnership _out1472;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1471, out _out1472);
                r = _out1471;
                resultingOwnership = _out1472;
              }
              readIdents = _4123_recIdents;
            } else {
              RAST._IExpr _4125_onExpr;
              DCOMP._IOwnership _4126_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4127_recIdents;
              RAST._IExpr _out1473;
              DCOMP._IOwnership _out1474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1475;
              (this).GenExpr(_4120_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1473, out _out1474, out _out1475);
              _4125_onExpr = _out1473;
              _4126_onOwned = _out1474;
              _4127_recIdents = _out1475;
              r = _4125_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4119_field));
              if (_4118_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4128_s;
                _4128_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4125_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4119_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4128_s);
              }
              DCOMP._IOwnership _4129_fromOwnership;
              _4129_fromOwnership = ((_4118_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1476;
              DCOMP._IOwnership _out1477;
              DCOMP.COMP.FromOwnership(r, _4129_fromOwnership, expectedOwnership, out _out1476, out _out1477);
              r = _out1476;
              resultingOwnership = _out1477;
              readIdents = _4127_recIdents;
            }
            return ;
          }
        } else if (_source174.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4130___mcc_h57 = _source174.dtor_Companion_i_a0;
          DAST._IType _4131_fieldType = _4099___mcc_h52;
          bool _4132_isDatatype = _4098___mcc_h51;
          bool _4133_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4134_field = _4096___mcc_h49;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4135_c = _4130___mcc_h57;
          {
            RAST._IExpr _4136_onExpr;
            DCOMP._IOwnership _4137_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4138_recIdents;
            RAST._IExpr _out1478;
            DCOMP._IOwnership _out1479;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1480;
            (this).GenExpr(DAST.Expression.create_Companion(_4135_c), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1478, out _out1479, out _out1480);
            _4136_onExpr = _out1478;
            _4137_onOwned = _out1479;
            _4138_recIdents = _out1480;
            r = ((_4136_onExpr).MSel(DCOMP.__default.escapeName(_4134_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out1481;
            DCOMP._IOwnership _out1482;
            DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1481, out _out1482);
            r = _out1481;
            resultingOwnership = _out1482;
            readIdents = _4138_recIdents;
            return ;
          }
        } else if (_source174.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _4139___mcc_h59 = _source174.dtor_Tuple_i_a0;
          DAST._IType _4140_fieldType = _4099___mcc_h52;
          bool _4141_isDatatype = _4098___mcc_h51;
          bool _4142_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4143_field = _4096___mcc_h49;
          DAST._IExpression _4144_on = _4095___mcc_h48;
          {
            if (_4141_isDatatype) {
              RAST._IExpr _4145_onExpr;
              DCOMP._IOwnership _4146_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4147_recIdents;
              RAST._IExpr _out1483;
              DCOMP._IOwnership _out1484;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1485;
              (this).GenExpr(_4144_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1483, out _out1484, out _out1485);
              _4145_onExpr = _out1483;
              _4146_onOwned = _out1484;
              _4147_recIdents = _out1485;
              r = ((_4145_onExpr).Sel(DCOMP.__default.escapeName(_4143_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4148_typ;
              RAST._IType _out1486;
              _out1486 = (this).GenType(_4140_fieldType, false, false);
              _4148_typ = _out1486;
              if (((_4148_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1487;
                DCOMP._IOwnership _out1488;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1487, out _out1488);
                r = _out1487;
                resultingOwnership = _out1488;
              }
              readIdents = _4147_recIdents;
            } else {
              RAST._IExpr _4149_onExpr;
              DCOMP._IOwnership _4150_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4151_recIdents;
              RAST._IExpr _out1489;
              DCOMP._IOwnership _out1490;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1491;
              (this).GenExpr(_4144_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1489, out _out1490, out _out1491);
              _4149_onExpr = _out1489;
              _4150_onOwned = _out1490;
              _4151_recIdents = _out1491;
              r = _4149_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4143_field));
              if (_4142_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4152_s;
                _4152_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4149_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4143_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4152_s);
              }
              DCOMP._IOwnership _4153_fromOwnership;
              _4153_fromOwnership = ((_4142_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1492;
              DCOMP._IOwnership _out1493;
              DCOMP.COMP.FromOwnership(r, _4153_fromOwnership, expectedOwnership, out _out1492, out _out1493);
              r = _out1492;
              resultingOwnership = _out1493;
              readIdents = _4151_recIdents;
            }
            return ;
          }
        } else if (_source174.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4154___mcc_h61 = _source174.dtor_path;
          Dafny.ISequence<DAST._IType> _4155___mcc_h62 = _source174.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _4156___mcc_h63 = _source174.dtor_args;
          DAST._IType _4157_fieldType = _4099___mcc_h52;
          bool _4158_isDatatype = _4098___mcc_h51;
          bool _4159_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4160_field = _4096___mcc_h49;
          DAST._IExpression _4161_on = _4095___mcc_h48;
          {
            if (_4158_isDatatype) {
              RAST._IExpr _4162_onExpr;
              DCOMP._IOwnership _4163_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4164_recIdents;
              RAST._IExpr _out1494;
              DCOMP._IOwnership _out1495;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1496;
              (this).GenExpr(_4161_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1494, out _out1495, out _out1496);
              _4162_onExpr = _out1494;
              _4163_onOwned = _out1495;
              _4164_recIdents = _out1496;
              r = ((_4162_onExpr).Sel(DCOMP.__default.escapeName(_4160_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4165_typ;
              RAST._IType _out1497;
              _out1497 = (this).GenType(_4157_fieldType, false, false);
              _4165_typ = _out1497;
              if (((_4165_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1498;
                DCOMP._IOwnership _out1499;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1498, out _out1499);
                r = _out1498;
                resultingOwnership = _out1499;
              }
              readIdents = _4164_recIdents;
            } else {
              RAST._IExpr _4166_onExpr;
              DCOMP._IOwnership _4167_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4168_recIdents;
              RAST._IExpr _out1500;
              DCOMP._IOwnership _out1501;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1502;
              (this).GenExpr(_4161_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1500, out _out1501, out _out1502);
              _4166_onExpr = _out1500;
              _4167_onOwned = _out1501;
              _4168_recIdents = _out1502;
              r = _4166_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4160_field));
              if (_4159_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4169_s;
                _4169_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4166_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4160_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4169_s);
              }
              DCOMP._IOwnership _4170_fromOwnership;
              _4170_fromOwnership = ((_4159_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1503;
              DCOMP._IOwnership _out1504;
              DCOMP.COMP.FromOwnership(r, _4170_fromOwnership, expectedOwnership, out _out1503, out _out1504);
              r = _out1503;
              resultingOwnership = _out1504;
              readIdents = _4168_recIdents;
            }
            return ;
          }
        } else if (_source174.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _4171___mcc_h67 = _source174.dtor_dims;
          DAST._IType _4172___mcc_h68 = _source174.dtor_typ;
          DAST._IType _4173_fieldType = _4099___mcc_h52;
          bool _4174_isDatatype = _4098___mcc_h51;
          bool _4175_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4176_field = _4096___mcc_h49;
          DAST._IExpression _4177_on = _4095___mcc_h48;
          {
            if (_4174_isDatatype) {
              RAST._IExpr _4178_onExpr;
              DCOMP._IOwnership _4179_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4180_recIdents;
              RAST._IExpr _out1505;
              DCOMP._IOwnership _out1506;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1507;
              (this).GenExpr(_4177_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1505, out _out1506, out _out1507);
              _4178_onExpr = _out1505;
              _4179_onOwned = _out1506;
              _4180_recIdents = _out1507;
              r = ((_4178_onExpr).Sel(DCOMP.__default.escapeName(_4176_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4181_typ;
              RAST._IType _out1508;
              _out1508 = (this).GenType(_4173_fieldType, false, false);
              _4181_typ = _out1508;
              if (((_4181_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1509;
                DCOMP._IOwnership _out1510;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1509, out _out1510);
                r = _out1509;
                resultingOwnership = _out1510;
              }
              readIdents = _4180_recIdents;
            } else {
              RAST._IExpr _4182_onExpr;
              DCOMP._IOwnership _4183_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4184_recIdents;
              RAST._IExpr _out1511;
              DCOMP._IOwnership _out1512;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1513;
              (this).GenExpr(_4177_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1511, out _out1512, out _out1513);
              _4182_onExpr = _out1511;
              _4183_onOwned = _out1512;
              _4184_recIdents = _out1513;
              r = _4182_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4176_field));
              if (_4175_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4185_s;
                _4185_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4182_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4176_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4185_s);
              }
              DCOMP._IOwnership _4186_fromOwnership;
              _4186_fromOwnership = ((_4175_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1514;
              DCOMP._IOwnership _out1515;
              DCOMP.COMP.FromOwnership(r, _4186_fromOwnership, expectedOwnership, out _out1514, out _out1515);
              r = _out1514;
              resultingOwnership = _out1515;
              readIdents = _4184_recIdents;
            }
            return ;
          }
        } else if (_source174.is_DatatypeValue) {
          DAST._IDatatypeType _4187___mcc_h71 = _source174.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _4188___mcc_h72 = _source174.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _4189___mcc_h73 = _source174.dtor_variant;
          bool _4190___mcc_h74 = _source174.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _4191___mcc_h75 = _source174.dtor_contents;
          DAST._IType _4192_fieldType = _4099___mcc_h52;
          bool _4193_isDatatype = _4098___mcc_h51;
          bool _4194_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4195_field = _4096___mcc_h49;
          DAST._IExpression _4196_on = _4095___mcc_h48;
          {
            if (_4193_isDatatype) {
              RAST._IExpr _4197_onExpr;
              DCOMP._IOwnership _4198_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4199_recIdents;
              RAST._IExpr _out1516;
              DCOMP._IOwnership _out1517;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1518;
              (this).GenExpr(_4196_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1516, out _out1517, out _out1518);
              _4197_onExpr = _out1516;
              _4198_onOwned = _out1517;
              _4199_recIdents = _out1518;
              r = ((_4197_onExpr).Sel(DCOMP.__default.escapeName(_4195_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4200_typ;
              RAST._IType _out1519;
              _out1519 = (this).GenType(_4192_fieldType, false, false);
              _4200_typ = _out1519;
              if (((_4200_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1520;
                DCOMP._IOwnership _out1521;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1520, out _out1521);
                r = _out1520;
                resultingOwnership = _out1521;
              }
              readIdents = _4199_recIdents;
            } else {
              RAST._IExpr _4201_onExpr;
              DCOMP._IOwnership _4202_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4203_recIdents;
              RAST._IExpr _out1522;
              DCOMP._IOwnership _out1523;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1524;
              (this).GenExpr(_4196_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1522, out _out1523, out _out1524);
              _4201_onExpr = _out1522;
              _4202_onOwned = _out1523;
              _4203_recIdents = _out1524;
              r = _4201_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4195_field));
              if (_4194_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4204_s;
                _4204_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4201_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4195_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4204_s);
              }
              DCOMP._IOwnership _4205_fromOwnership;
              _4205_fromOwnership = ((_4194_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1525;
              DCOMP._IOwnership _out1526;
              DCOMP.COMP.FromOwnership(r, _4205_fromOwnership, expectedOwnership, out _out1525, out _out1526);
              r = _out1525;
              resultingOwnership = _out1526;
              readIdents = _4203_recIdents;
            }
            return ;
          }
        } else if (_source174.is_Convert) {
          DAST._IExpression _4206___mcc_h81 = _source174.dtor_value;
          DAST._IType _4207___mcc_h82 = _source174.dtor_from;
          DAST._IType _4208___mcc_h83 = _source174.dtor_typ;
          DAST._IType _4209_fieldType = _4099___mcc_h52;
          bool _4210_isDatatype = _4098___mcc_h51;
          bool _4211_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4212_field = _4096___mcc_h49;
          DAST._IExpression _4213_on = _4095___mcc_h48;
          {
            if (_4210_isDatatype) {
              RAST._IExpr _4214_onExpr;
              DCOMP._IOwnership _4215_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4216_recIdents;
              RAST._IExpr _out1527;
              DCOMP._IOwnership _out1528;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1529;
              (this).GenExpr(_4213_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1527, out _out1528, out _out1529);
              _4214_onExpr = _out1527;
              _4215_onOwned = _out1528;
              _4216_recIdents = _out1529;
              r = ((_4214_onExpr).Sel(DCOMP.__default.escapeName(_4212_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4217_typ;
              RAST._IType _out1530;
              _out1530 = (this).GenType(_4209_fieldType, false, false);
              _4217_typ = _out1530;
              if (((_4217_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1531;
                DCOMP._IOwnership _out1532;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1531, out _out1532);
                r = _out1531;
                resultingOwnership = _out1532;
              }
              readIdents = _4216_recIdents;
            } else {
              RAST._IExpr _4218_onExpr;
              DCOMP._IOwnership _4219_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4220_recIdents;
              RAST._IExpr _out1533;
              DCOMP._IOwnership _out1534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1535;
              (this).GenExpr(_4213_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1533, out _out1534, out _out1535);
              _4218_onExpr = _out1533;
              _4219_onOwned = _out1534;
              _4220_recIdents = _out1535;
              r = _4218_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4212_field));
              if (_4211_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4221_s;
                _4221_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4218_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4212_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4221_s);
              }
              DCOMP._IOwnership _4222_fromOwnership;
              _4222_fromOwnership = ((_4211_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1536;
              DCOMP._IOwnership _out1537;
              DCOMP.COMP.FromOwnership(r, _4222_fromOwnership, expectedOwnership, out _out1536, out _out1537);
              r = _out1536;
              resultingOwnership = _out1537;
              readIdents = _4220_recIdents;
            }
            return ;
          }
        } else if (_source174.is_SeqConstruct) {
          DAST._IExpression _4223___mcc_h87 = _source174.dtor_length;
          DAST._IExpression _4224___mcc_h88 = _source174.dtor_elem;
          DAST._IType _4225_fieldType = _4099___mcc_h52;
          bool _4226_isDatatype = _4098___mcc_h51;
          bool _4227_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4228_field = _4096___mcc_h49;
          DAST._IExpression _4229_on = _4095___mcc_h48;
          {
            if (_4226_isDatatype) {
              RAST._IExpr _4230_onExpr;
              DCOMP._IOwnership _4231_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4232_recIdents;
              RAST._IExpr _out1538;
              DCOMP._IOwnership _out1539;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1540;
              (this).GenExpr(_4229_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1538, out _out1539, out _out1540);
              _4230_onExpr = _out1538;
              _4231_onOwned = _out1539;
              _4232_recIdents = _out1540;
              r = ((_4230_onExpr).Sel(DCOMP.__default.escapeName(_4228_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4233_typ;
              RAST._IType _out1541;
              _out1541 = (this).GenType(_4225_fieldType, false, false);
              _4233_typ = _out1541;
              if (((_4233_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1542;
                DCOMP._IOwnership _out1543;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1542, out _out1543);
                r = _out1542;
                resultingOwnership = _out1543;
              }
              readIdents = _4232_recIdents;
            } else {
              RAST._IExpr _4234_onExpr;
              DCOMP._IOwnership _4235_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4236_recIdents;
              RAST._IExpr _out1544;
              DCOMP._IOwnership _out1545;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1546;
              (this).GenExpr(_4229_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1544, out _out1545, out _out1546);
              _4234_onExpr = _out1544;
              _4235_onOwned = _out1545;
              _4236_recIdents = _out1546;
              r = _4234_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4228_field));
              if (_4227_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4237_s;
                _4237_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4234_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4228_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4237_s);
              }
              DCOMP._IOwnership _4238_fromOwnership;
              _4238_fromOwnership = ((_4227_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1547;
              DCOMP._IOwnership _out1548;
              DCOMP.COMP.FromOwnership(r, _4238_fromOwnership, expectedOwnership, out _out1547, out _out1548);
              r = _out1547;
              resultingOwnership = _out1548;
              readIdents = _4236_recIdents;
            }
            return ;
          }
        } else if (_source174.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _4239___mcc_h91 = _source174.dtor_elements;
          DAST._IType _4240___mcc_h92 = _source174.dtor_typ;
          DAST._IType _4241_fieldType = _4099___mcc_h52;
          bool _4242_isDatatype = _4098___mcc_h51;
          bool _4243_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4244_field = _4096___mcc_h49;
          DAST._IExpression _4245_on = _4095___mcc_h48;
          {
            if (_4242_isDatatype) {
              RAST._IExpr _4246_onExpr;
              DCOMP._IOwnership _4247_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4248_recIdents;
              RAST._IExpr _out1549;
              DCOMP._IOwnership _out1550;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1551;
              (this).GenExpr(_4245_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1549, out _out1550, out _out1551);
              _4246_onExpr = _out1549;
              _4247_onOwned = _out1550;
              _4248_recIdents = _out1551;
              r = ((_4246_onExpr).Sel(DCOMP.__default.escapeName(_4244_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4249_typ;
              RAST._IType _out1552;
              _out1552 = (this).GenType(_4241_fieldType, false, false);
              _4249_typ = _out1552;
              if (((_4249_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1553;
                DCOMP._IOwnership _out1554;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1553, out _out1554);
                r = _out1553;
                resultingOwnership = _out1554;
              }
              readIdents = _4248_recIdents;
            } else {
              RAST._IExpr _4250_onExpr;
              DCOMP._IOwnership _4251_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4252_recIdents;
              RAST._IExpr _out1555;
              DCOMP._IOwnership _out1556;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1557;
              (this).GenExpr(_4245_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1555, out _out1556, out _out1557);
              _4250_onExpr = _out1555;
              _4251_onOwned = _out1556;
              _4252_recIdents = _out1557;
              r = _4250_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4244_field));
              if (_4243_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4253_s;
                _4253_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4250_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4244_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4253_s);
              }
              DCOMP._IOwnership _4254_fromOwnership;
              _4254_fromOwnership = ((_4243_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1558;
              DCOMP._IOwnership _out1559;
              DCOMP.COMP.FromOwnership(r, _4254_fromOwnership, expectedOwnership, out _out1558, out _out1559);
              r = _out1558;
              resultingOwnership = _out1559;
              readIdents = _4252_recIdents;
            }
            return ;
          }
        } else if (_source174.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _4255___mcc_h95 = _source174.dtor_elements;
          DAST._IType _4256_fieldType = _4099___mcc_h52;
          bool _4257_isDatatype = _4098___mcc_h51;
          bool _4258_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4259_field = _4096___mcc_h49;
          DAST._IExpression _4260_on = _4095___mcc_h48;
          {
            if (_4257_isDatatype) {
              RAST._IExpr _4261_onExpr;
              DCOMP._IOwnership _4262_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4263_recIdents;
              RAST._IExpr _out1560;
              DCOMP._IOwnership _out1561;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1562;
              (this).GenExpr(_4260_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1560, out _out1561, out _out1562);
              _4261_onExpr = _out1560;
              _4262_onOwned = _out1561;
              _4263_recIdents = _out1562;
              r = ((_4261_onExpr).Sel(DCOMP.__default.escapeName(_4259_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4264_typ;
              RAST._IType _out1563;
              _out1563 = (this).GenType(_4256_fieldType, false, false);
              _4264_typ = _out1563;
              if (((_4264_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1564;
                DCOMP._IOwnership _out1565;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1564, out _out1565);
                r = _out1564;
                resultingOwnership = _out1565;
              }
              readIdents = _4263_recIdents;
            } else {
              RAST._IExpr _4265_onExpr;
              DCOMP._IOwnership _4266_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4267_recIdents;
              RAST._IExpr _out1566;
              DCOMP._IOwnership _out1567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1568;
              (this).GenExpr(_4260_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1566, out _out1567, out _out1568);
              _4265_onExpr = _out1566;
              _4266_onOwned = _out1567;
              _4267_recIdents = _out1568;
              r = _4265_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4259_field));
              if (_4258_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4268_s;
                _4268_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4265_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4259_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4268_s);
              }
              DCOMP._IOwnership _4269_fromOwnership;
              _4269_fromOwnership = ((_4258_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1569;
              DCOMP._IOwnership _out1570;
              DCOMP.COMP.FromOwnership(r, _4269_fromOwnership, expectedOwnership, out _out1569, out _out1570);
              r = _out1569;
              resultingOwnership = _out1570;
              readIdents = _4267_recIdents;
            }
            return ;
          }
        } else if (_source174.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _4270___mcc_h97 = _source174.dtor_elements;
          DAST._IType _4271_fieldType = _4099___mcc_h52;
          bool _4272_isDatatype = _4098___mcc_h51;
          bool _4273_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4274_field = _4096___mcc_h49;
          DAST._IExpression _4275_on = _4095___mcc_h48;
          {
            if (_4272_isDatatype) {
              RAST._IExpr _4276_onExpr;
              DCOMP._IOwnership _4277_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4278_recIdents;
              RAST._IExpr _out1571;
              DCOMP._IOwnership _out1572;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1573;
              (this).GenExpr(_4275_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1571, out _out1572, out _out1573);
              _4276_onExpr = _out1571;
              _4277_onOwned = _out1572;
              _4278_recIdents = _out1573;
              r = ((_4276_onExpr).Sel(DCOMP.__default.escapeName(_4274_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4279_typ;
              RAST._IType _out1574;
              _out1574 = (this).GenType(_4271_fieldType, false, false);
              _4279_typ = _out1574;
              if (((_4279_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1575;
                DCOMP._IOwnership _out1576;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1575, out _out1576);
                r = _out1575;
                resultingOwnership = _out1576;
              }
              readIdents = _4278_recIdents;
            } else {
              RAST._IExpr _4280_onExpr;
              DCOMP._IOwnership _4281_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4282_recIdents;
              RAST._IExpr _out1577;
              DCOMP._IOwnership _out1578;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1579;
              (this).GenExpr(_4275_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1577, out _out1578, out _out1579);
              _4280_onExpr = _out1577;
              _4281_onOwned = _out1578;
              _4282_recIdents = _out1579;
              r = _4280_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4274_field));
              if (_4273_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4283_s;
                _4283_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4280_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4274_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4283_s);
              }
              DCOMP._IOwnership _4284_fromOwnership;
              _4284_fromOwnership = ((_4273_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1580;
              DCOMP._IOwnership _out1581;
              DCOMP.COMP.FromOwnership(r, _4284_fromOwnership, expectedOwnership, out _out1580, out _out1581);
              r = _out1580;
              resultingOwnership = _out1581;
              readIdents = _4282_recIdents;
            }
            return ;
          }
        } else if (_source174.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4285___mcc_h99 = _source174.dtor_mapElems;
          DAST._IType _4286_fieldType = _4099___mcc_h52;
          bool _4287_isDatatype = _4098___mcc_h51;
          bool _4288_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4289_field = _4096___mcc_h49;
          DAST._IExpression _4290_on = _4095___mcc_h48;
          {
            if (_4287_isDatatype) {
              RAST._IExpr _4291_onExpr;
              DCOMP._IOwnership _4292_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4293_recIdents;
              RAST._IExpr _out1582;
              DCOMP._IOwnership _out1583;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1584;
              (this).GenExpr(_4290_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1582, out _out1583, out _out1584);
              _4291_onExpr = _out1582;
              _4292_onOwned = _out1583;
              _4293_recIdents = _out1584;
              r = ((_4291_onExpr).Sel(DCOMP.__default.escapeName(_4289_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4294_typ;
              RAST._IType _out1585;
              _out1585 = (this).GenType(_4286_fieldType, false, false);
              _4294_typ = _out1585;
              if (((_4294_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1586;
                DCOMP._IOwnership _out1587;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1586, out _out1587);
                r = _out1586;
                resultingOwnership = _out1587;
              }
              readIdents = _4293_recIdents;
            } else {
              RAST._IExpr _4295_onExpr;
              DCOMP._IOwnership _4296_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4297_recIdents;
              RAST._IExpr _out1588;
              DCOMP._IOwnership _out1589;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1590;
              (this).GenExpr(_4290_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1588, out _out1589, out _out1590);
              _4295_onExpr = _out1588;
              _4296_onOwned = _out1589;
              _4297_recIdents = _out1590;
              r = _4295_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4289_field));
              if (_4288_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4298_s;
                _4298_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4295_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4289_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4298_s);
              }
              DCOMP._IOwnership _4299_fromOwnership;
              _4299_fromOwnership = ((_4288_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1591;
              DCOMP._IOwnership _out1592;
              DCOMP.COMP.FromOwnership(r, _4299_fromOwnership, expectedOwnership, out _out1591, out _out1592);
              r = _out1591;
              resultingOwnership = _out1592;
              readIdents = _4297_recIdents;
            }
            return ;
          }
        } else if (_source174.is_MapBuilder) {
          DAST._IType _4300___mcc_h101 = _source174.dtor_keyType;
          DAST._IType _4301___mcc_h102 = _source174.dtor_valueType;
          DAST._IType _4302_fieldType = _4099___mcc_h52;
          bool _4303_isDatatype = _4098___mcc_h51;
          bool _4304_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4305_field = _4096___mcc_h49;
          DAST._IExpression _4306_on = _4095___mcc_h48;
          {
            if (_4303_isDatatype) {
              RAST._IExpr _4307_onExpr;
              DCOMP._IOwnership _4308_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4309_recIdents;
              RAST._IExpr _out1593;
              DCOMP._IOwnership _out1594;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1595;
              (this).GenExpr(_4306_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1593, out _out1594, out _out1595);
              _4307_onExpr = _out1593;
              _4308_onOwned = _out1594;
              _4309_recIdents = _out1595;
              r = ((_4307_onExpr).Sel(DCOMP.__default.escapeName(_4305_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4310_typ;
              RAST._IType _out1596;
              _out1596 = (this).GenType(_4302_fieldType, false, false);
              _4310_typ = _out1596;
              if (((_4310_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1597;
                DCOMP._IOwnership _out1598;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1597, out _out1598);
                r = _out1597;
                resultingOwnership = _out1598;
              }
              readIdents = _4309_recIdents;
            } else {
              RAST._IExpr _4311_onExpr;
              DCOMP._IOwnership _4312_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4313_recIdents;
              RAST._IExpr _out1599;
              DCOMP._IOwnership _out1600;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1601;
              (this).GenExpr(_4306_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1599, out _out1600, out _out1601);
              _4311_onExpr = _out1599;
              _4312_onOwned = _out1600;
              _4313_recIdents = _out1601;
              r = _4311_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4305_field));
              if (_4304_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4314_s;
                _4314_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4311_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4305_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4314_s);
              }
              DCOMP._IOwnership _4315_fromOwnership;
              _4315_fromOwnership = ((_4304_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1602;
              DCOMP._IOwnership _out1603;
              DCOMP.COMP.FromOwnership(r, _4315_fromOwnership, expectedOwnership, out _out1602, out _out1603);
              r = _out1602;
              resultingOwnership = _out1603;
              readIdents = _4313_recIdents;
            }
            return ;
          }
        } else if (_source174.is_SeqUpdate) {
          DAST._IExpression _4316___mcc_h105 = _source174.dtor_expr;
          DAST._IExpression _4317___mcc_h106 = _source174.dtor_indexExpr;
          DAST._IExpression _4318___mcc_h107 = _source174.dtor_value;
          DAST._IType _4319_fieldType = _4099___mcc_h52;
          bool _4320_isDatatype = _4098___mcc_h51;
          bool _4321_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4322_field = _4096___mcc_h49;
          DAST._IExpression _4323_on = _4095___mcc_h48;
          {
            if (_4320_isDatatype) {
              RAST._IExpr _4324_onExpr;
              DCOMP._IOwnership _4325_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4326_recIdents;
              RAST._IExpr _out1604;
              DCOMP._IOwnership _out1605;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1606;
              (this).GenExpr(_4323_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1604, out _out1605, out _out1606);
              _4324_onExpr = _out1604;
              _4325_onOwned = _out1605;
              _4326_recIdents = _out1606;
              r = ((_4324_onExpr).Sel(DCOMP.__default.escapeName(_4322_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4327_typ;
              RAST._IType _out1607;
              _out1607 = (this).GenType(_4319_fieldType, false, false);
              _4327_typ = _out1607;
              if (((_4327_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1608;
                DCOMP._IOwnership _out1609;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1608, out _out1609);
                r = _out1608;
                resultingOwnership = _out1609;
              }
              readIdents = _4326_recIdents;
            } else {
              RAST._IExpr _4328_onExpr;
              DCOMP._IOwnership _4329_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4330_recIdents;
              RAST._IExpr _out1610;
              DCOMP._IOwnership _out1611;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1612;
              (this).GenExpr(_4323_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1610, out _out1611, out _out1612);
              _4328_onExpr = _out1610;
              _4329_onOwned = _out1611;
              _4330_recIdents = _out1612;
              r = _4328_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4322_field));
              if (_4321_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4331_s;
                _4331_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4328_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4322_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4331_s);
              }
              DCOMP._IOwnership _4332_fromOwnership;
              _4332_fromOwnership = ((_4321_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1613;
              DCOMP._IOwnership _out1614;
              DCOMP.COMP.FromOwnership(r, _4332_fromOwnership, expectedOwnership, out _out1613, out _out1614);
              r = _out1613;
              resultingOwnership = _out1614;
              readIdents = _4330_recIdents;
            }
            return ;
          }
        } else if (_source174.is_MapUpdate) {
          DAST._IExpression _4333___mcc_h111 = _source174.dtor_expr;
          DAST._IExpression _4334___mcc_h112 = _source174.dtor_indexExpr;
          DAST._IExpression _4335___mcc_h113 = _source174.dtor_value;
          DAST._IType _4336_fieldType = _4099___mcc_h52;
          bool _4337_isDatatype = _4098___mcc_h51;
          bool _4338_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4339_field = _4096___mcc_h49;
          DAST._IExpression _4340_on = _4095___mcc_h48;
          {
            if (_4337_isDatatype) {
              RAST._IExpr _4341_onExpr;
              DCOMP._IOwnership _4342_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4343_recIdents;
              RAST._IExpr _out1615;
              DCOMP._IOwnership _out1616;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1617;
              (this).GenExpr(_4340_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1615, out _out1616, out _out1617);
              _4341_onExpr = _out1615;
              _4342_onOwned = _out1616;
              _4343_recIdents = _out1617;
              r = ((_4341_onExpr).Sel(DCOMP.__default.escapeName(_4339_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4344_typ;
              RAST._IType _out1618;
              _out1618 = (this).GenType(_4336_fieldType, false, false);
              _4344_typ = _out1618;
              if (((_4344_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1619;
                DCOMP._IOwnership _out1620;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1619, out _out1620);
                r = _out1619;
                resultingOwnership = _out1620;
              }
              readIdents = _4343_recIdents;
            } else {
              RAST._IExpr _4345_onExpr;
              DCOMP._IOwnership _4346_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4347_recIdents;
              RAST._IExpr _out1621;
              DCOMP._IOwnership _out1622;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1623;
              (this).GenExpr(_4340_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1621, out _out1622, out _out1623);
              _4345_onExpr = _out1621;
              _4346_onOwned = _out1622;
              _4347_recIdents = _out1623;
              r = _4345_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4339_field));
              if (_4338_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4348_s;
                _4348_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4345_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4339_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4348_s);
              }
              DCOMP._IOwnership _4349_fromOwnership;
              _4349_fromOwnership = ((_4338_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1624;
              DCOMP._IOwnership _out1625;
              DCOMP.COMP.FromOwnership(r, _4349_fromOwnership, expectedOwnership, out _out1624, out _out1625);
              r = _out1624;
              resultingOwnership = _out1625;
              readIdents = _4347_recIdents;
            }
            return ;
          }
        } else if (_source174.is_SetBuilder) {
          DAST._IType _4350___mcc_h117 = _source174.dtor_elemType;
          DAST._IType _4351_fieldType = _4099___mcc_h52;
          bool _4352_isDatatype = _4098___mcc_h51;
          bool _4353_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4354_field = _4096___mcc_h49;
          DAST._IExpression _4355_on = _4095___mcc_h48;
          {
            if (_4352_isDatatype) {
              RAST._IExpr _4356_onExpr;
              DCOMP._IOwnership _4357_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4358_recIdents;
              RAST._IExpr _out1626;
              DCOMP._IOwnership _out1627;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1628;
              (this).GenExpr(_4355_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1626, out _out1627, out _out1628);
              _4356_onExpr = _out1626;
              _4357_onOwned = _out1627;
              _4358_recIdents = _out1628;
              r = ((_4356_onExpr).Sel(DCOMP.__default.escapeName(_4354_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4359_typ;
              RAST._IType _out1629;
              _out1629 = (this).GenType(_4351_fieldType, false, false);
              _4359_typ = _out1629;
              if (((_4359_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1630;
                DCOMP._IOwnership _out1631;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1630, out _out1631);
                r = _out1630;
                resultingOwnership = _out1631;
              }
              readIdents = _4358_recIdents;
            } else {
              RAST._IExpr _4360_onExpr;
              DCOMP._IOwnership _4361_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4362_recIdents;
              RAST._IExpr _out1632;
              DCOMP._IOwnership _out1633;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1634;
              (this).GenExpr(_4355_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1632, out _out1633, out _out1634);
              _4360_onExpr = _out1632;
              _4361_onOwned = _out1633;
              _4362_recIdents = _out1634;
              r = _4360_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4354_field));
              if (_4353_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4363_s;
                _4363_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4360_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4354_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4363_s);
              }
              DCOMP._IOwnership _4364_fromOwnership;
              _4364_fromOwnership = ((_4353_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1635;
              DCOMP._IOwnership _out1636;
              DCOMP.COMP.FromOwnership(r, _4364_fromOwnership, expectedOwnership, out _out1635, out _out1636);
              r = _out1635;
              resultingOwnership = _out1636;
              readIdents = _4362_recIdents;
            }
            return ;
          }
        } else if (_source174.is_ToMultiset) {
          DAST._IExpression _4365___mcc_h119 = _source174.dtor_ToMultiset_i_a0;
          DAST._IType _4366_fieldType = _4099___mcc_h52;
          bool _4367_isDatatype = _4098___mcc_h51;
          bool _4368_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4369_field = _4096___mcc_h49;
          DAST._IExpression _4370_on = _4095___mcc_h48;
          {
            if (_4367_isDatatype) {
              RAST._IExpr _4371_onExpr;
              DCOMP._IOwnership _4372_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4373_recIdents;
              RAST._IExpr _out1637;
              DCOMP._IOwnership _out1638;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1639;
              (this).GenExpr(_4370_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1637, out _out1638, out _out1639);
              _4371_onExpr = _out1637;
              _4372_onOwned = _out1638;
              _4373_recIdents = _out1639;
              r = ((_4371_onExpr).Sel(DCOMP.__default.escapeName(_4369_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4374_typ;
              RAST._IType _out1640;
              _out1640 = (this).GenType(_4366_fieldType, false, false);
              _4374_typ = _out1640;
              if (((_4374_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1641;
                DCOMP._IOwnership _out1642;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1641, out _out1642);
                r = _out1641;
                resultingOwnership = _out1642;
              }
              readIdents = _4373_recIdents;
            } else {
              RAST._IExpr _4375_onExpr;
              DCOMP._IOwnership _4376_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4377_recIdents;
              RAST._IExpr _out1643;
              DCOMP._IOwnership _out1644;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1645;
              (this).GenExpr(_4370_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1643, out _out1644, out _out1645);
              _4375_onExpr = _out1643;
              _4376_onOwned = _out1644;
              _4377_recIdents = _out1645;
              r = _4375_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4369_field));
              if (_4368_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4378_s;
                _4378_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4375_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4369_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4378_s);
              }
              DCOMP._IOwnership _4379_fromOwnership;
              _4379_fromOwnership = ((_4368_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1646;
              DCOMP._IOwnership _out1647;
              DCOMP.COMP.FromOwnership(r, _4379_fromOwnership, expectedOwnership, out _out1646, out _out1647);
              r = _out1646;
              resultingOwnership = _out1647;
              readIdents = _4377_recIdents;
            }
            return ;
          }
        } else if (_source174.is_This) {
          DAST._IType _4380_fieldType = _4099___mcc_h52;
          bool _4381_isDatatype = _4098___mcc_h51;
          bool _4382_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4383_field = _4096___mcc_h49;
          DAST._IExpression _4384_on = _4095___mcc_h48;
          {
            if (_4381_isDatatype) {
              RAST._IExpr _4385_onExpr;
              DCOMP._IOwnership _4386_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4387_recIdents;
              RAST._IExpr _out1648;
              DCOMP._IOwnership _out1649;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1650;
              (this).GenExpr(_4384_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1648, out _out1649, out _out1650);
              _4385_onExpr = _out1648;
              _4386_onOwned = _out1649;
              _4387_recIdents = _out1650;
              r = ((_4385_onExpr).Sel(DCOMP.__default.escapeName(_4383_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4388_typ;
              RAST._IType _out1651;
              _out1651 = (this).GenType(_4380_fieldType, false, false);
              _4388_typ = _out1651;
              if (((_4388_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1652;
                DCOMP._IOwnership _out1653;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1652, out _out1653);
                r = _out1652;
                resultingOwnership = _out1653;
              }
              readIdents = _4387_recIdents;
            } else {
              RAST._IExpr _4389_onExpr;
              DCOMP._IOwnership _4390_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4391_recIdents;
              RAST._IExpr _out1654;
              DCOMP._IOwnership _out1655;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1656;
              (this).GenExpr(_4384_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1654, out _out1655, out _out1656);
              _4389_onExpr = _out1654;
              _4390_onOwned = _out1655;
              _4391_recIdents = _out1656;
              r = _4389_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4383_field));
              if (_4382_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4392_s;
                _4392_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4389_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4383_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4392_s);
              }
              DCOMP._IOwnership _4393_fromOwnership;
              _4393_fromOwnership = ((_4382_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1657;
              DCOMP._IOwnership _out1658;
              DCOMP.COMP.FromOwnership(r, _4393_fromOwnership, expectedOwnership, out _out1657, out _out1658);
              r = _out1657;
              resultingOwnership = _out1658;
              readIdents = _4391_recIdents;
            }
            return ;
          }
        } else if (_source174.is_Ite) {
          DAST._IExpression _4394___mcc_h121 = _source174.dtor_cond;
          DAST._IExpression _4395___mcc_h122 = _source174.dtor_thn;
          DAST._IExpression _4396___mcc_h123 = _source174.dtor_els;
          DAST._IType _4397_fieldType = _4099___mcc_h52;
          bool _4398_isDatatype = _4098___mcc_h51;
          bool _4399_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4400_field = _4096___mcc_h49;
          DAST._IExpression _4401_on = _4095___mcc_h48;
          {
            if (_4398_isDatatype) {
              RAST._IExpr _4402_onExpr;
              DCOMP._IOwnership _4403_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4404_recIdents;
              RAST._IExpr _out1659;
              DCOMP._IOwnership _out1660;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1661;
              (this).GenExpr(_4401_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1659, out _out1660, out _out1661);
              _4402_onExpr = _out1659;
              _4403_onOwned = _out1660;
              _4404_recIdents = _out1661;
              r = ((_4402_onExpr).Sel(DCOMP.__default.escapeName(_4400_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4405_typ;
              RAST._IType _out1662;
              _out1662 = (this).GenType(_4397_fieldType, false, false);
              _4405_typ = _out1662;
              if (((_4405_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1663;
                DCOMP._IOwnership _out1664;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1663, out _out1664);
                r = _out1663;
                resultingOwnership = _out1664;
              }
              readIdents = _4404_recIdents;
            } else {
              RAST._IExpr _4406_onExpr;
              DCOMP._IOwnership _4407_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4408_recIdents;
              RAST._IExpr _out1665;
              DCOMP._IOwnership _out1666;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1667;
              (this).GenExpr(_4401_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1665, out _out1666, out _out1667);
              _4406_onExpr = _out1665;
              _4407_onOwned = _out1666;
              _4408_recIdents = _out1667;
              r = _4406_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4400_field));
              if (_4399_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4409_s;
                _4409_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4406_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4400_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4409_s);
              }
              DCOMP._IOwnership _4410_fromOwnership;
              _4410_fromOwnership = ((_4399_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1668;
              DCOMP._IOwnership _out1669;
              DCOMP.COMP.FromOwnership(r, _4410_fromOwnership, expectedOwnership, out _out1668, out _out1669);
              r = _out1668;
              resultingOwnership = _out1669;
              readIdents = _4408_recIdents;
            }
            return ;
          }
        } else if (_source174.is_UnOp) {
          DAST._IUnaryOp _4411___mcc_h127 = _source174.dtor_unOp;
          DAST._IExpression _4412___mcc_h128 = _source174.dtor_expr;
          DAST.Format._IUnaryOpFormat _4413___mcc_h129 = _source174.dtor_format1;
          DAST._IType _4414_fieldType = _4099___mcc_h52;
          bool _4415_isDatatype = _4098___mcc_h51;
          bool _4416_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4417_field = _4096___mcc_h49;
          DAST._IExpression _4418_on = _4095___mcc_h48;
          {
            if (_4415_isDatatype) {
              RAST._IExpr _4419_onExpr;
              DCOMP._IOwnership _4420_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4421_recIdents;
              RAST._IExpr _out1670;
              DCOMP._IOwnership _out1671;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1672;
              (this).GenExpr(_4418_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1670, out _out1671, out _out1672);
              _4419_onExpr = _out1670;
              _4420_onOwned = _out1671;
              _4421_recIdents = _out1672;
              r = ((_4419_onExpr).Sel(DCOMP.__default.escapeName(_4417_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4422_typ;
              RAST._IType _out1673;
              _out1673 = (this).GenType(_4414_fieldType, false, false);
              _4422_typ = _out1673;
              if (((_4422_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1674;
                DCOMP._IOwnership _out1675;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1674, out _out1675);
                r = _out1674;
                resultingOwnership = _out1675;
              }
              readIdents = _4421_recIdents;
            } else {
              RAST._IExpr _4423_onExpr;
              DCOMP._IOwnership _4424_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4425_recIdents;
              RAST._IExpr _out1676;
              DCOMP._IOwnership _out1677;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1678;
              (this).GenExpr(_4418_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1676, out _out1677, out _out1678);
              _4423_onExpr = _out1676;
              _4424_onOwned = _out1677;
              _4425_recIdents = _out1678;
              r = _4423_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4417_field));
              if (_4416_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4426_s;
                _4426_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4423_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4417_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4426_s);
              }
              DCOMP._IOwnership _4427_fromOwnership;
              _4427_fromOwnership = ((_4416_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1679;
              DCOMP._IOwnership _out1680;
              DCOMP.COMP.FromOwnership(r, _4427_fromOwnership, expectedOwnership, out _out1679, out _out1680);
              r = _out1679;
              resultingOwnership = _out1680;
              readIdents = _4425_recIdents;
            }
            return ;
          }
        } else if (_source174.is_BinOp) {
          DAST._IBinOp _4428___mcc_h133 = _source174.dtor_op;
          DAST._IExpression _4429___mcc_h134 = _source174.dtor_left;
          DAST._IExpression _4430___mcc_h135 = _source174.dtor_right;
          DAST.Format._IBinaryOpFormat _4431___mcc_h136 = _source174.dtor_format2;
          DAST._IType _4432_fieldType = _4099___mcc_h52;
          bool _4433_isDatatype = _4098___mcc_h51;
          bool _4434_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4435_field = _4096___mcc_h49;
          DAST._IExpression _4436_on = _4095___mcc_h48;
          {
            if (_4433_isDatatype) {
              RAST._IExpr _4437_onExpr;
              DCOMP._IOwnership _4438_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4439_recIdents;
              RAST._IExpr _out1681;
              DCOMP._IOwnership _out1682;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1683;
              (this).GenExpr(_4436_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1681, out _out1682, out _out1683);
              _4437_onExpr = _out1681;
              _4438_onOwned = _out1682;
              _4439_recIdents = _out1683;
              r = ((_4437_onExpr).Sel(DCOMP.__default.escapeName(_4435_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4440_typ;
              RAST._IType _out1684;
              _out1684 = (this).GenType(_4432_fieldType, false, false);
              _4440_typ = _out1684;
              if (((_4440_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1685;
                DCOMP._IOwnership _out1686;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1685, out _out1686);
                r = _out1685;
                resultingOwnership = _out1686;
              }
              readIdents = _4439_recIdents;
            } else {
              RAST._IExpr _4441_onExpr;
              DCOMP._IOwnership _4442_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4443_recIdents;
              RAST._IExpr _out1687;
              DCOMP._IOwnership _out1688;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1689;
              (this).GenExpr(_4436_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1687, out _out1688, out _out1689);
              _4441_onExpr = _out1687;
              _4442_onOwned = _out1688;
              _4443_recIdents = _out1689;
              r = _4441_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4435_field));
              if (_4434_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4444_s;
                _4444_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4441_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4435_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4444_s);
              }
              DCOMP._IOwnership _4445_fromOwnership;
              _4445_fromOwnership = ((_4434_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1690;
              DCOMP._IOwnership _out1691;
              DCOMP.COMP.FromOwnership(r, _4445_fromOwnership, expectedOwnership, out _out1690, out _out1691);
              r = _out1690;
              resultingOwnership = _out1691;
              readIdents = _4443_recIdents;
            }
            return ;
          }
        } else if (_source174.is_ArrayLen) {
          DAST._IExpression _4446___mcc_h141 = _source174.dtor_expr;
          BigInteger _4447___mcc_h142 = _source174.dtor_dim;
          DAST._IType _4448_fieldType = _4099___mcc_h52;
          bool _4449_isDatatype = _4098___mcc_h51;
          bool _4450_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4451_field = _4096___mcc_h49;
          DAST._IExpression _4452_on = _4095___mcc_h48;
          {
            if (_4449_isDatatype) {
              RAST._IExpr _4453_onExpr;
              DCOMP._IOwnership _4454_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4455_recIdents;
              RAST._IExpr _out1692;
              DCOMP._IOwnership _out1693;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1694;
              (this).GenExpr(_4452_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1692, out _out1693, out _out1694);
              _4453_onExpr = _out1692;
              _4454_onOwned = _out1693;
              _4455_recIdents = _out1694;
              r = ((_4453_onExpr).Sel(DCOMP.__default.escapeName(_4451_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4456_typ;
              RAST._IType _out1695;
              _out1695 = (this).GenType(_4448_fieldType, false, false);
              _4456_typ = _out1695;
              if (((_4456_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1696;
                DCOMP._IOwnership _out1697;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1696, out _out1697);
                r = _out1696;
                resultingOwnership = _out1697;
              }
              readIdents = _4455_recIdents;
            } else {
              RAST._IExpr _4457_onExpr;
              DCOMP._IOwnership _4458_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4459_recIdents;
              RAST._IExpr _out1698;
              DCOMP._IOwnership _out1699;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1700;
              (this).GenExpr(_4452_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1698, out _out1699, out _out1700);
              _4457_onExpr = _out1698;
              _4458_onOwned = _out1699;
              _4459_recIdents = _out1700;
              r = _4457_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4451_field));
              if (_4450_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4460_s;
                _4460_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4457_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4451_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4460_s);
              }
              DCOMP._IOwnership _4461_fromOwnership;
              _4461_fromOwnership = ((_4450_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1701;
              DCOMP._IOwnership _out1702;
              DCOMP.COMP.FromOwnership(r, _4461_fromOwnership, expectedOwnership, out _out1701, out _out1702);
              r = _out1701;
              resultingOwnership = _out1702;
              readIdents = _4459_recIdents;
            }
            return ;
          }
        } else if (_source174.is_MapKeys) {
          DAST._IExpression _4462___mcc_h145 = _source174.dtor_expr;
          DAST._IType _4463_fieldType = _4099___mcc_h52;
          bool _4464_isDatatype = _4098___mcc_h51;
          bool _4465_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4466_field = _4096___mcc_h49;
          DAST._IExpression _4467_on = _4095___mcc_h48;
          {
            if (_4464_isDatatype) {
              RAST._IExpr _4468_onExpr;
              DCOMP._IOwnership _4469_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4470_recIdents;
              RAST._IExpr _out1703;
              DCOMP._IOwnership _out1704;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1705;
              (this).GenExpr(_4467_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1703, out _out1704, out _out1705);
              _4468_onExpr = _out1703;
              _4469_onOwned = _out1704;
              _4470_recIdents = _out1705;
              r = ((_4468_onExpr).Sel(DCOMP.__default.escapeName(_4466_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4471_typ;
              RAST._IType _out1706;
              _out1706 = (this).GenType(_4463_fieldType, false, false);
              _4471_typ = _out1706;
              if (((_4471_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1707;
                DCOMP._IOwnership _out1708;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1707, out _out1708);
                r = _out1707;
                resultingOwnership = _out1708;
              }
              readIdents = _4470_recIdents;
            } else {
              RAST._IExpr _4472_onExpr;
              DCOMP._IOwnership _4473_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4474_recIdents;
              RAST._IExpr _out1709;
              DCOMP._IOwnership _out1710;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1711;
              (this).GenExpr(_4467_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1709, out _out1710, out _out1711);
              _4472_onExpr = _out1709;
              _4473_onOwned = _out1710;
              _4474_recIdents = _out1711;
              r = _4472_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4466_field));
              if (_4465_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4475_s;
                _4475_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4472_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4466_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4475_s);
              }
              DCOMP._IOwnership _4476_fromOwnership;
              _4476_fromOwnership = ((_4465_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1712;
              DCOMP._IOwnership _out1713;
              DCOMP.COMP.FromOwnership(r, _4476_fromOwnership, expectedOwnership, out _out1712, out _out1713);
              r = _out1712;
              resultingOwnership = _out1713;
              readIdents = _4474_recIdents;
            }
            return ;
          }
        } else if (_source174.is_MapValues) {
          DAST._IExpression _4477___mcc_h147 = _source174.dtor_expr;
          DAST._IType _4478_fieldType = _4099___mcc_h52;
          bool _4479_isDatatype = _4098___mcc_h51;
          bool _4480_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4481_field = _4096___mcc_h49;
          DAST._IExpression _4482_on = _4095___mcc_h48;
          {
            if (_4479_isDatatype) {
              RAST._IExpr _4483_onExpr;
              DCOMP._IOwnership _4484_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4485_recIdents;
              RAST._IExpr _out1714;
              DCOMP._IOwnership _out1715;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1716;
              (this).GenExpr(_4482_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1714, out _out1715, out _out1716);
              _4483_onExpr = _out1714;
              _4484_onOwned = _out1715;
              _4485_recIdents = _out1716;
              r = ((_4483_onExpr).Sel(DCOMP.__default.escapeName(_4481_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4486_typ;
              RAST._IType _out1717;
              _out1717 = (this).GenType(_4478_fieldType, false, false);
              _4486_typ = _out1717;
              if (((_4486_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1718;
                DCOMP._IOwnership _out1719;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1718, out _out1719);
                r = _out1718;
                resultingOwnership = _out1719;
              }
              readIdents = _4485_recIdents;
            } else {
              RAST._IExpr _4487_onExpr;
              DCOMP._IOwnership _4488_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4489_recIdents;
              RAST._IExpr _out1720;
              DCOMP._IOwnership _out1721;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1722;
              (this).GenExpr(_4482_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1720, out _out1721, out _out1722);
              _4487_onExpr = _out1720;
              _4488_onOwned = _out1721;
              _4489_recIdents = _out1722;
              r = _4487_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4481_field));
              if (_4480_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4490_s;
                _4490_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4487_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4481_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4490_s);
              }
              DCOMP._IOwnership _4491_fromOwnership;
              _4491_fromOwnership = ((_4480_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1723;
              DCOMP._IOwnership _out1724;
              DCOMP.COMP.FromOwnership(r, _4491_fromOwnership, expectedOwnership, out _out1723, out _out1724);
              r = _out1723;
              resultingOwnership = _out1724;
              readIdents = _4489_recIdents;
            }
            return ;
          }
        } else if (_source174.is_Select) {
          DAST._IExpression _4492___mcc_h149 = _source174.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _4493___mcc_h150 = _source174.dtor_field;
          bool _4494___mcc_h151 = _source174.dtor_isConstant;
          bool _4495___mcc_h152 = _source174.dtor_onDatatype;
          DAST._IType _4496___mcc_h153 = _source174.dtor_fieldType;
          DAST._IType _4497_fieldType = _4099___mcc_h52;
          bool _4498_isDatatype = _4098___mcc_h51;
          bool _4499_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4500_field = _4096___mcc_h49;
          DAST._IExpression _4501_on = _4095___mcc_h48;
          {
            if (_4498_isDatatype) {
              RAST._IExpr _4502_onExpr;
              DCOMP._IOwnership _4503_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4504_recIdents;
              RAST._IExpr _out1725;
              DCOMP._IOwnership _out1726;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1727;
              (this).GenExpr(_4501_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1725, out _out1726, out _out1727);
              _4502_onExpr = _out1725;
              _4503_onOwned = _out1726;
              _4504_recIdents = _out1727;
              r = ((_4502_onExpr).Sel(DCOMP.__default.escapeName(_4500_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4505_typ;
              RAST._IType _out1728;
              _out1728 = (this).GenType(_4497_fieldType, false, false);
              _4505_typ = _out1728;
              if (((_4505_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1729;
                DCOMP._IOwnership _out1730;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1729, out _out1730);
                r = _out1729;
                resultingOwnership = _out1730;
              }
              readIdents = _4504_recIdents;
            } else {
              RAST._IExpr _4506_onExpr;
              DCOMP._IOwnership _4507_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4508_recIdents;
              RAST._IExpr _out1731;
              DCOMP._IOwnership _out1732;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1733;
              (this).GenExpr(_4501_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1731, out _out1732, out _out1733);
              _4506_onExpr = _out1731;
              _4507_onOwned = _out1732;
              _4508_recIdents = _out1733;
              r = _4506_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4500_field));
              if (_4499_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4509_s;
                _4509_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4506_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4500_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4509_s);
              }
              DCOMP._IOwnership _4510_fromOwnership;
              _4510_fromOwnership = ((_4499_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1734;
              DCOMP._IOwnership _out1735;
              DCOMP.COMP.FromOwnership(r, _4510_fromOwnership, expectedOwnership, out _out1734, out _out1735);
              r = _out1734;
              resultingOwnership = _out1735;
              readIdents = _4508_recIdents;
            }
            return ;
          }
        } else if (_source174.is_SelectFn) {
          DAST._IExpression _4511___mcc_h159 = _source174.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _4512___mcc_h160 = _source174.dtor_field;
          bool _4513___mcc_h161 = _source174.dtor_onDatatype;
          bool _4514___mcc_h162 = _source174.dtor_isStatic;
          BigInteger _4515___mcc_h163 = _source174.dtor_arity;
          DAST._IType _4516_fieldType = _4099___mcc_h52;
          bool _4517_isDatatype = _4098___mcc_h51;
          bool _4518_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4519_field = _4096___mcc_h49;
          DAST._IExpression _4520_on = _4095___mcc_h48;
          {
            if (_4517_isDatatype) {
              RAST._IExpr _4521_onExpr;
              DCOMP._IOwnership _4522_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4523_recIdents;
              RAST._IExpr _out1736;
              DCOMP._IOwnership _out1737;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1738;
              (this).GenExpr(_4520_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1736, out _out1737, out _out1738);
              _4521_onExpr = _out1736;
              _4522_onOwned = _out1737;
              _4523_recIdents = _out1738;
              r = ((_4521_onExpr).Sel(DCOMP.__default.escapeName(_4519_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4524_typ;
              RAST._IType _out1739;
              _out1739 = (this).GenType(_4516_fieldType, false, false);
              _4524_typ = _out1739;
              if (((_4524_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1740;
                DCOMP._IOwnership _out1741;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1740, out _out1741);
                r = _out1740;
                resultingOwnership = _out1741;
              }
              readIdents = _4523_recIdents;
            } else {
              RAST._IExpr _4525_onExpr;
              DCOMP._IOwnership _4526_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4527_recIdents;
              RAST._IExpr _out1742;
              DCOMP._IOwnership _out1743;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1744;
              (this).GenExpr(_4520_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1742, out _out1743, out _out1744);
              _4525_onExpr = _out1742;
              _4526_onOwned = _out1743;
              _4527_recIdents = _out1744;
              r = _4525_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4519_field));
              if (_4518_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4528_s;
                _4528_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4525_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4519_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4528_s);
              }
              DCOMP._IOwnership _4529_fromOwnership;
              _4529_fromOwnership = ((_4518_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1745;
              DCOMP._IOwnership _out1746;
              DCOMP.COMP.FromOwnership(r, _4529_fromOwnership, expectedOwnership, out _out1745, out _out1746);
              r = _out1745;
              resultingOwnership = _out1746;
              readIdents = _4527_recIdents;
            }
            return ;
          }
        } else if (_source174.is_Index) {
          DAST._IExpression _4530___mcc_h169 = _source174.dtor_expr;
          DAST._ICollKind _4531___mcc_h170 = _source174.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _4532___mcc_h171 = _source174.dtor_indices;
          DAST._IType _4533_fieldType = _4099___mcc_h52;
          bool _4534_isDatatype = _4098___mcc_h51;
          bool _4535_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4536_field = _4096___mcc_h49;
          DAST._IExpression _4537_on = _4095___mcc_h48;
          {
            if (_4534_isDatatype) {
              RAST._IExpr _4538_onExpr;
              DCOMP._IOwnership _4539_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4540_recIdents;
              RAST._IExpr _out1747;
              DCOMP._IOwnership _out1748;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1749;
              (this).GenExpr(_4537_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1747, out _out1748, out _out1749);
              _4538_onExpr = _out1747;
              _4539_onOwned = _out1748;
              _4540_recIdents = _out1749;
              r = ((_4538_onExpr).Sel(DCOMP.__default.escapeName(_4536_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4541_typ;
              RAST._IType _out1750;
              _out1750 = (this).GenType(_4533_fieldType, false, false);
              _4541_typ = _out1750;
              if (((_4541_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1751;
                DCOMP._IOwnership _out1752;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1751, out _out1752);
                r = _out1751;
                resultingOwnership = _out1752;
              }
              readIdents = _4540_recIdents;
            } else {
              RAST._IExpr _4542_onExpr;
              DCOMP._IOwnership _4543_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4544_recIdents;
              RAST._IExpr _out1753;
              DCOMP._IOwnership _out1754;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1755;
              (this).GenExpr(_4537_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1753, out _out1754, out _out1755);
              _4542_onExpr = _out1753;
              _4543_onOwned = _out1754;
              _4544_recIdents = _out1755;
              r = _4542_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4536_field));
              if (_4535_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4545_s;
                _4545_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4542_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4536_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4545_s);
              }
              DCOMP._IOwnership _4546_fromOwnership;
              _4546_fromOwnership = ((_4535_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1756;
              DCOMP._IOwnership _out1757;
              DCOMP.COMP.FromOwnership(r, _4546_fromOwnership, expectedOwnership, out _out1756, out _out1757);
              r = _out1756;
              resultingOwnership = _out1757;
              readIdents = _4544_recIdents;
            }
            return ;
          }
        } else if (_source174.is_IndexRange) {
          DAST._IExpression _4547___mcc_h175 = _source174.dtor_expr;
          bool _4548___mcc_h176 = _source174.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _4549___mcc_h177 = _source174.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _4550___mcc_h178 = _source174.dtor_high;
          DAST._IType _4551_fieldType = _4099___mcc_h52;
          bool _4552_isDatatype = _4098___mcc_h51;
          bool _4553_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4554_field = _4096___mcc_h49;
          DAST._IExpression _4555_on = _4095___mcc_h48;
          {
            if (_4552_isDatatype) {
              RAST._IExpr _4556_onExpr;
              DCOMP._IOwnership _4557_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4558_recIdents;
              RAST._IExpr _out1758;
              DCOMP._IOwnership _out1759;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1760;
              (this).GenExpr(_4555_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1758, out _out1759, out _out1760);
              _4556_onExpr = _out1758;
              _4557_onOwned = _out1759;
              _4558_recIdents = _out1760;
              r = ((_4556_onExpr).Sel(DCOMP.__default.escapeName(_4554_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4559_typ;
              RAST._IType _out1761;
              _out1761 = (this).GenType(_4551_fieldType, false, false);
              _4559_typ = _out1761;
              if (((_4559_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1762;
                DCOMP._IOwnership _out1763;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1762, out _out1763);
                r = _out1762;
                resultingOwnership = _out1763;
              }
              readIdents = _4558_recIdents;
            } else {
              RAST._IExpr _4560_onExpr;
              DCOMP._IOwnership _4561_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4562_recIdents;
              RAST._IExpr _out1764;
              DCOMP._IOwnership _out1765;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1766;
              (this).GenExpr(_4555_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1764, out _out1765, out _out1766);
              _4560_onExpr = _out1764;
              _4561_onOwned = _out1765;
              _4562_recIdents = _out1766;
              r = _4560_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4554_field));
              if (_4553_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4563_s;
                _4563_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4560_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4554_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4563_s);
              }
              DCOMP._IOwnership _4564_fromOwnership;
              _4564_fromOwnership = ((_4553_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1767;
              DCOMP._IOwnership _out1768;
              DCOMP.COMP.FromOwnership(r, _4564_fromOwnership, expectedOwnership, out _out1767, out _out1768);
              r = _out1767;
              resultingOwnership = _out1768;
              readIdents = _4562_recIdents;
            }
            return ;
          }
        } else if (_source174.is_TupleSelect) {
          DAST._IExpression _4565___mcc_h183 = _source174.dtor_expr;
          BigInteger _4566___mcc_h184 = _source174.dtor_index;
          DAST._IType _4567___mcc_h185 = _source174.dtor_fieldType;
          DAST._IType _4568_fieldType = _4099___mcc_h52;
          bool _4569_isDatatype = _4098___mcc_h51;
          bool _4570_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4571_field = _4096___mcc_h49;
          DAST._IExpression _4572_on = _4095___mcc_h48;
          {
            if (_4569_isDatatype) {
              RAST._IExpr _4573_onExpr;
              DCOMP._IOwnership _4574_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4575_recIdents;
              RAST._IExpr _out1769;
              DCOMP._IOwnership _out1770;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1771;
              (this).GenExpr(_4572_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1769, out _out1770, out _out1771);
              _4573_onExpr = _out1769;
              _4574_onOwned = _out1770;
              _4575_recIdents = _out1771;
              r = ((_4573_onExpr).Sel(DCOMP.__default.escapeName(_4571_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4576_typ;
              RAST._IType _out1772;
              _out1772 = (this).GenType(_4568_fieldType, false, false);
              _4576_typ = _out1772;
              if (((_4576_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1773;
                DCOMP._IOwnership _out1774;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1773, out _out1774);
                r = _out1773;
                resultingOwnership = _out1774;
              }
              readIdents = _4575_recIdents;
            } else {
              RAST._IExpr _4577_onExpr;
              DCOMP._IOwnership _4578_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4579_recIdents;
              RAST._IExpr _out1775;
              DCOMP._IOwnership _out1776;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1777;
              (this).GenExpr(_4572_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1775, out _out1776, out _out1777);
              _4577_onExpr = _out1775;
              _4578_onOwned = _out1776;
              _4579_recIdents = _out1777;
              r = _4577_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4571_field));
              if (_4570_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4580_s;
                _4580_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4577_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4571_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4580_s);
              }
              DCOMP._IOwnership _4581_fromOwnership;
              _4581_fromOwnership = ((_4570_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1778;
              DCOMP._IOwnership _out1779;
              DCOMP.COMP.FromOwnership(r, _4581_fromOwnership, expectedOwnership, out _out1778, out _out1779);
              r = _out1778;
              resultingOwnership = _out1779;
              readIdents = _4579_recIdents;
            }
            return ;
          }
        } else if (_source174.is_Call) {
          DAST._IExpression _4582___mcc_h189 = _source174.dtor_on;
          DAST._ICallName _4583___mcc_h190 = _source174.dtor_callName;
          Dafny.ISequence<DAST._IType> _4584___mcc_h191 = _source174.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _4585___mcc_h192 = _source174.dtor_args;
          DAST._IType _4586_fieldType = _4099___mcc_h52;
          bool _4587_isDatatype = _4098___mcc_h51;
          bool _4588_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4589_field = _4096___mcc_h49;
          DAST._IExpression _4590_on = _4095___mcc_h48;
          {
            if (_4587_isDatatype) {
              RAST._IExpr _4591_onExpr;
              DCOMP._IOwnership _4592_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4593_recIdents;
              RAST._IExpr _out1780;
              DCOMP._IOwnership _out1781;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1782;
              (this).GenExpr(_4590_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1780, out _out1781, out _out1782);
              _4591_onExpr = _out1780;
              _4592_onOwned = _out1781;
              _4593_recIdents = _out1782;
              r = ((_4591_onExpr).Sel(DCOMP.__default.escapeName(_4589_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4594_typ;
              RAST._IType _out1783;
              _out1783 = (this).GenType(_4586_fieldType, false, false);
              _4594_typ = _out1783;
              if (((_4594_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1784;
                DCOMP._IOwnership _out1785;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1784, out _out1785);
                r = _out1784;
                resultingOwnership = _out1785;
              }
              readIdents = _4593_recIdents;
            } else {
              RAST._IExpr _4595_onExpr;
              DCOMP._IOwnership _4596_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4597_recIdents;
              RAST._IExpr _out1786;
              DCOMP._IOwnership _out1787;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1788;
              (this).GenExpr(_4590_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1786, out _out1787, out _out1788);
              _4595_onExpr = _out1786;
              _4596_onOwned = _out1787;
              _4597_recIdents = _out1788;
              r = _4595_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4589_field));
              if (_4588_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4598_s;
                _4598_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4595_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4589_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4598_s);
              }
              DCOMP._IOwnership _4599_fromOwnership;
              _4599_fromOwnership = ((_4588_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1789;
              DCOMP._IOwnership _out1790;
              DCOMP.COMP.FromOwnership(r, _4599_fromOwnership, expectedOwnership, out _out1789, out _out1790);
              r = _out1789;
              resultingOwnership = _out1790;
              readIdents = _4597_recIdents;
            }
            return ;
          }
        } else if (_source174.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _4600___mcc_h197 = _source174.dtor_params;
          DAST._IType _4601___mcc_h198 = _source174.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _4602___mcc_h199 = _source174.dtor_body;
          DAST._IType _4603_fieldType = _4099___mcc_h52;
          bool _4604_isDatatype = _4098___mcc_h51;
          bool _4605_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4606_field = _4096___mcc_h49;
          DAST._IExpression _4607_on = _4095___mcc_h48;
          {
            if (_4604_isDatatype) {
              RAST._IExpr _4608_onExpr;
              DCOMP._IOwnership _4609_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4610_recIdents;
              RAST._IExpr _out1791;
              DCOMP._IOwnership _out1792;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1793;
              (this).GenExpr(_4607_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1791, out _out1792, out _out1793);
              _4608_onExpr = _out1791;
              _4609_onOwned = _out1792;
              _4610_recIdents = _out1793;
              r = ((_4608_onExpr).Sel(DCOMP.__default.escapeName(_4606_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4611_typ;
              RAST._IType _out1794;
              _out1794 = (this).GenType(_4603_fieldType, false, false);
              _4611_typ = _out1794;
              if (((_4611_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1795;
                DCOMP._IOwnership _out1796;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1795, out _out1796);
                r = _out1795;
                resultingOwnership = _out1796;
              }
              readIdents = _4610_recIdents;
            } else {
              RAST._IExpr _4612_onExpr;
              DCOMP._IOwnership _4613_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4614_recIdents;
              RAST._IExpr _out1797;
              DCOMP._IOwnership _out1798;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1799;
              (this).GenExpr(_4607_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1797, out _out1798, out _out1799);
              _4612_onExpr = _out1797;
              _4613_onOwned = _out1798;
              _4614_recIdents = _out1799;
              r = _4612_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4606_field));
              if (_4605_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4615_s;
                _4615_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4612_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4606_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4615_s);
              }
              DCOMP._IOwnership _4616_fromOwnership;
              _4616_fromOwnership = ((_4605_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1800;
              DCOMP._IOwnership _out1801;
              DCOMP.COMP.FromOwnership(r, _4616_fromOwnership, expectedOwnership, out _out1800, out _out1801);
              r = _out1800;
              resultingOwnership = _out1801;
              readIdents = _4614_recIdents;
            }
            return ;
          }
        } else if (_source174.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4617___mcc_h203 = _source174.dtor_values;
          DAST._IType _4618___mcc_h204 = _source174.dtor_retType;
          DAST._IExpression _4619___mcc_h205 = _source174.dtor_expr;
          DAST._IType _4620_fieldType = _4099___mcc_h52;
          bool _4621_isDatatype = _4098___mcc_h51;
          bool _4622_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4623_field = _4096___mcc_h49;
          DAST._IExpression _4624_on = _4095___mcc_h48;
          {
            if (_4621_isDatatype) {
              RAST._IExpr _4625_onExpr;
              DCOMP._IOwnership _4626_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4627_recIdents;
              RAST._IExpr _out1802;
              DCOMP._IOwnership _out1803;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1804;
              (this).GenExpr(_4624_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1802, out _out1803, out _out1804);
              _4625_onExpr = _out1802;
              _4626_onOwned = _out1803;
              _4627_recIdents = _out1804;
              r = ((_4625_onExpr).Sel(DCOMP.__default.escapeName(_4623_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4628_typ;
              RAST._IType _out1805;
              _out1805 = (this).GenType(_4620_fieldType, false, false);
              _4628_typ = _out1805;
              if (((_4628_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1806;
                DCOMP._IOwnership _out1807;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1806, out _out1807);
                r = _out1806;
                resultingOwnership = _out1807;
              }
              readIdents = _4627_recIdents;
            } else {
              RAST._IExpr _4629_onExpr;
              DCOMP._IOwnership _4630_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4631_recIdents;
              RAST._IExpr _out1808;
              DCOMP._IOwnership _out1809;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1810;
              (this).GenExpr(_4624_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1808, out _out1809, out _out1810);
              _4629_onExpr = _out1808;
              _4630_onOwned = _out1809;
              _4631_recIdents = _out1810;
              r = _4629_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4623_field));
              if (_4622_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4632_s;
                _4632_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4629_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4623_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4632_s);
              }
              DCOMP._IOwnership _4633_fromOwnership;
              _4633_fromOwnership = ((_4622_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1811;
              DCOMP._IOwnership _out1812;
              DCOMP.COMP.FromOwnership(r, _4633_fromOwnership, expectedOwnership, out _out1811, out _out1812);
              r = _out1811;
              resultingOwnership = _out1812;
              readIdents = _4631_recIdents;
            }
            return ;
          }
        } else if (_source174.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _4634___mcc_h209 = _source174.dtor_name;
          DAST._IType _4635___mcc_h210 = _source174.dtor_typ;
          DAST._IExpression _4636___mcc_h211 = _source174.dtor_value;
          DAST._IExpression _4637___mcc_h212 = _source174.dtor_iifeBody;
          DAST._IType _4638_fieldType = _4099___mcc_h52;
          bool _4639_isDatatype = _4098___mcc_h51;
          bool _4640_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4641_field = _4096___mcc_h49;
          DAST._IExpression _4642_on = _4095___mcc_h48;
          {
            if (_4639_isDatatype) {
              RAST._IExpr _4643_onExpr;
              DCOMP._IOwnership _4644_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4645_recIdents;
              RAST._IExpr _out1813;
              DCOMP._IOwnership _out1814;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1815;
              (this).GenExpr(_4642_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1813, out _out1814, out _out1815);
              _4643_onExpr = _out1813;
              _4644_onOwned = _out1814;
              _4645_recIdents = _out1815;
              r = ((_4643_onExpr).Sel(DCOMP.__default.escapeName(_4641_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4646_typ;
              RAST._IType _out1816;
              _out1816 = (this).GenType(_4638_fieldType, false, false);
              _4646_typ = _out1816;
              if (((_4646_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1817;
                DCOMP._IOwnership _out1818;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1817, out _out1818);
                r = _out1817;
                resultingOwnership = _out1818;
              }
              readIdents = _4645_recIdents;
            } else {
              RAST._IExpr _4647_onExpr;
              DCOMP._IOwnership _4648_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4649_recIdents;
              RAST._IExpr _out1819;
              DCOMP._IOwnership _out1820;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1821;
              (this).GenExpr(_4642_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1819, out _out1820, out _out1821);
              _4647_onExpr = _out1819;
              _4648_onOwned = _out1820;
              _4649_recIdents = _out1821;
              r = _4647_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4641_field));
              if (_4640_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4650_s;
                _4650_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4647_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4641_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4650_s);
              }
              DCOMP._IOwnership _4651_fromOwnership;
              _4651_fromOwnership = ((_4640_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1822;
              DCOMP._IOwnership _out1823;
              DCOMP.COMP.FromOwnership(r, _4651_fromOwnership, expectedOwnership, out _out1822, out _out1823);
              r = _out1822;
              resultingOwnership = _out1823;
              readIdents = _4649_recIdents;
            }
            return ;
          }
        } else if (_source174.is_Apply) {
          DAST._IExpression _4652___mcc_h217 = _source174.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _4653___mcc_h218 = _source174.dtor_args;
          DAST._IType _4654_fieldType = _4099___mcc_h52;
          bool _4655_isDatatype = _4098___mcc_h51;
          bool _4656_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4657_field = _4096___mcc_h49;
          DAST._IExpression _4658_on = _4095___mcc_h48;
          {
            if (_4655_isDatatype) {
              RAST._IExpr _4659_onExpr;
              DCOMP._IOwnership _4660_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4661_recIdents;
              RAST._IExpr _out1824;
              DCOMP._IOwnership _out1825;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1826;
              (this).GenExpr(_4658_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1824, out _out1825, out _out1826);
              _4659_onExpr = _out1824;
              _4660_onOwned = _out1825;
              _4661_recIdents = _out1826;
              r = ((_4659_onExpr).Sel(DCOMP.__default.escapeName(_4657_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4662_typ;
              RAST._IType _out1827;
              _out1827 = (this).GenType(_4654_fieldType, false, false);
              _4662_typ = _out1827;
              if (((_4662_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1828;
                DCOMP._IOwnership _out1829;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1828, out _out1829);
                r = _out1828;
                resultingOwnership = _out1829;
              }
              readIdents = _4661_recIdents;
            } else {
              RAST._IExpr _4663_onExpr;
              DCOMP._IOwnership _4664_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4665_recIdents;
              RAST._IExpr _out1830;
              DCOMP._IOwnership _out1831;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1832;
              (this).GenExpr(_4658_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1830, out _out1831, out _out1832);
              _4663_onExpr = _out1830;
              _4664_onOwned = _out1831;
              _4665_recIdents = _out1832;
              r = _4663_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4657_field));
              if (_4656_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4666_s;
                _4666_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4663_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4657_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4666_s);
              }
              DCOMP._IOwnership _4667_fromOwnership;
              _4667_fromOwnership = ((_4656_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1833;
              DCOMP._IOwnership _out1834;
              DCOMP.COMP.FromOwnership(r, _4667_fromOwnership, expectedOwnership, out _out1833, out _out1834);
              r = _out1833;
              resultingOwnership = _out1834;
              readIdents = _4665_recIdents;
            }
            return ;
          }
        } else if (_source174.is_TypeTest) {
          DAST._IExpression _4668___mcc_h221 = _source174.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4669___mcc_h222 = _source174.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _4670___mcc_h223 = _source174.dtor_variant;
          DAST._IType _4671_fieldType = _4099___mcc_h52;
          bool _4672_isDatatype = _4098___mcc_h51;
          bool _4673_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4674_field = _4096___mcc_h49;
          DAST._IExpression _4675_on = _4095___mcc_h48;
          {
            if (_4672_isDatatype) {
              RAST._IExpr _4676_onExpr;
              DCOMP._IOwnership _4677_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4678_recIdents;
              RAST._IExpr _out1835;
              DCOMP._IOwnership _out1836;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1837;
              (this).GenExpr(_4675_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1835, out _out1836, out _out1837);
              _4676_onExpr = _out1835;
              _4677_onOwned = _out1836;
              _4678_recIdents = _out1837;
              r = ((_4676_onExpr).Sel(DCOMP.__default.escapeName(_4674_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4679_typ;
              RAST._IType _out1838;
              _out1838 = (this).GenType(_4671_fieldType, false, false);
              _4679_typ = _out1838;
              if (((_4679_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1839;
                DCOMP._IOwnership _out1840;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1839, out _out1840);
                r = _out1839;
                resultingOwnership = _out1840;
              }
              readIdents = _4678_recIdents;
            } else {
              RAST._IExpr _4680_onExpr;
              DCOMP._IOwnership _4681_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4682_recIdents;
              RAST._IExpr _out1841;
              DCOMP._IOwnership _out1842;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1843;
              (this).GenExpr(_4675_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1841, out _out1842, out _out1843);
              _4680_onExpr = _out1841;
              _4681_onOwned = _out1842;
              _4682_recIdents = _out1843;
              r = _4680_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4674_field));
              if (_4673_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4683_s;
                _4683_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4680_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4674_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4683_s);
              }
              DCOMP._IOwnership _4684_fromOwnership;
              _4684_fromOwnership = ((_4673_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1844;
              DCOMP._IOwnership _out1845;
              DCOMP.COMP.FromOwnership(r, _4684_fromOwnership, expectedOwnership, out _out1844, out _out1845);
              r = _out1844;
              resultingOwnership = _out1845;
              readIdents = _4682_recIdents;
            }
            return ;
          }
        } else if (_source174.is_InitializationValue) {
          DAST._IType _4685___mcc_h227 = _source174.dtor_typ;
          DAST._IType _4686_fieldType = _4099___mcc_h52;
          bool _4687_isDatatype = _4098___mcc_h51;
          bool _4688_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4689_field = _4096___mcc_h49;
          DAST._IExpression _4690_on = _4095___mcc_h48;
          {
            if (_4687_isDatatype) {
              RAST._IExpr _4691_onExpr;
              DCOMP._IOwnership _4692_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4693_recIdents;
              RAST._IExpr _out1846;
              DCOMP._IOwnership _out1847;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1848;
              (this).GenExpr(_4690_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1846, out _out1847, out _out1848);
              _4691_onExpr = _out1846;
              _4692_onOwned = _out1847;
              _4693_recIdents = _out1848;
              r = ((_4691_onExpr).Sel(DCOMP.__default.escapeName(_4689_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4694_typ;
              RAST._IType _out1849;
              _out1849 = (this).GenType(_4686_fieldType, false, false);
              _4694_typ = _out1849;
              if (((_4694_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1850;
                DCOMP._IOwnership _out1851;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1850, out _out1851);
                r = _out1850;
                resultingOwnership = _out1851;
              }
              readIdents = _4693_recIdents;
            } else {
              RAST._IExpr _4695_onExpr;
              DCOMP._IOwnership _4696_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4697_recIdents;
              RAST._IExpr _out1852;
              DCOMP._IOwnership _out1853;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1854;
              (this).GenExpr(_4690_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1852, out _out1853, out _out1854);
              _4695_onExpr = _out1852;
              _4696_onOwned = _out1853;
              _4697_recIdents = _out1854;
              r = _4695_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4689_field));
              if (_4688_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4698_s;
                _4698_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4695_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4689_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4698_s);
              }
              DCOMP._IOwnership _4699_fromOwnership;
              _4699_fromOwnership = ((_4688_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1855;
              DCOMP._IOwnership _out1856;
              DCOMP.COMP.FromOwnership(r, _4699_fromOwnership, expectedOwnership, out _out1855, out _out1856);
              r = _out1855;
              resultingOwnership = _out1856;
              readIdents = _4697_recIdents;
            }
            return ;
          }
        } else if (_source174.is_BoolBoundedPool) {
          DAST._IType _4700_fieldType = _4099___mcc_h52;
          bool _4701_isDatatype = _4098___mcc_h51;
          bool _4702_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4703_field = _4096___mcc_h49;
          DAST._IExpression _4704_on = _4095___mcc_h48;
          {
            if (_4701_isDatatype) {
              RAST._IExpr _4705_onExpr;
              DCOMP._IOwnership _4706_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4707_recIdents;
              RAST._IExpr _out1857;
              DCOMP._IOwnership _out1858;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1859;
              (this).GenExpr(_4704_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1857, out _out1858, out _out1859);
              _4705_onExpr = _out1857;
              _4706_onOwned = _out1858;
              _4707_recIdents = _out1859;
              r = ((_4705_onExpr).Sel(DCOMP.__default.escapeName(_4703_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4708_typ;
              RAST._IType _out1860;
              _out1860 = (this).GenType(_4700_fieldType, false, false);
              _4708_typ = _out1860;
              if (((_4708_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1861;
                DCOMP._IOwnership _out1862;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1861, out _out1862);
                r = _out1861;
                resultingOwnership = _out1862;
              }
              readIdents = _4707_recIdents;
            } else {
              RAST._IExpr _4709_onExpr;
              DCOMP._IOwnership _4710_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4711_recIdents;
              RAST._IExpr _out1863;
              DCOMP._IOwnership _out1864;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1865;
              (this).GenExpr(_4704_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1863, out _out1864, out _out1865);
              _4709_onExpr = _out1863;
              _4710_onOwned = _out1864;
              _4711_recIdents = _out1865;
              r = _4709_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4703_field));
              if (_4702_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4712_s;
                _4712_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4709_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4703_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4712_s);
              }
              DCOMP._IOwnership _4713_fromOwnership;
              _4713_fromOwnership = ((_4702_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1866;
              DCOMP._IOwnership _out1867;
              DCOMP.COMP.FromOwnership(r, _4713_fromOwnership, expectedOwnership, out _out1866, out _out1867);
              r = _out1866;
              resultingOwnership = _out1867;
              readIdents = _4711_recIdents;
            }
            return ;
          }
        } else if (_source174.is_SetBoundedPool) {
          DAST._IExpression _4714___mcc_h229 = _source174.dtor_of;
          DAST._IType _4715_fieldType = _4099___mcc_h52;
          bool _4716_isDatatype = _4098___mcc_h51;
          bool _4717_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4718_field = _4096___mcc_h49;
          DAST._IExpression _4719_on = _4095___mcc_h48;
          {
            if (_4716_isDatatype) {
              RAST._IExpr _4720_onExpr;
              DCOMP._IOwnership _4721_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4722_recIdents;
              RAST._IExpr _out1868;
              DCOMP._IOwnership _out1869;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1870;
              (this).GenExpr(_4719_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1868, out _out1869, out _out1870);
              _4720_onExpr = _out1868;
              _4721_onOwned = _out1869;
              _4722_recIdents = _out1870;
              r = ((_4720_onExpr).Sel(DCOMP.__default.escapeName(_4718_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4723_typ;
              RAST._IType _out1871;
              _out1871 = (this).GenType(_4715_fieldType, false, false);
              _4723_typ = _out1871;
              if (((_4723_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1872;
                DCOMP._IOwnership _out1873;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1872, out _out1873);
                r = _out1872;
                resultingOwnership = _out1873;
              }
              readIdents = _4722_recIdents;
            } else {
              RAST._IExpr _4724_onExpr;
              DCOMP._IOwnership _4725_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4726_recIdents;
              RAST._IExpr _out1874;
              DCOMP._IOwnership _out1875;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1876;
              (this).GenExpr(_4719_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1874, out _out1875, out _out1876);
              _4724_onExpr = _out1874;
              _4725_onOwned = _out1875;
              _4726_recIdents = _out1876;
              r = _4724_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4718_field));
              if (_4717_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4727_s;
                _4727_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4724_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4718_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4727_s);
              }
              DCOMP._IOwnership _4728_fromOwnership;
              _4728_fromOwnership = ((_4717_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1877;
              DCOMP._IOwnership _out1878;
              DCOMP.COMP.FromOwnership(r, _4728_fromOwnership, expectedOwnership, out _out1877, out _out1878);
              r = _out1877;
              resultingOwnership = _out1878;
              readIdents = _4726_recIdents;
            }
            return ;
          }
        } else if (_source174.is_SeqBoundedPool) {
          DAST._IExpression _4729___mcc_h231 = _source174.dtor_of;
          bool _4730___mcc_h232 = _source174.dtor_includeDuplicates;
          DAST._IType _4731_fieldType = _4099___mcc_h52;
          bool _4732_isDatatype = _4098___mcc_h51;
          bool _4733_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4734_field = _4096___mcc_h49;
          DAST._IExpression _4735_on = _4095___mcc_h48;
          {
            if (_4732_isDatatype) {
              RAST._IExpr _4736_onExpr;
              DCOMP._IOwnership _4737_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4738_recIdents;
              RAST._IExpr _out1879;
              DCOMP._IOwnership _out1880;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1881;
              (this).GenExpr(_4735_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1879, out _out1880, out _out1881);
              _4736_onExpr = _out1879;
              _4737_onOwned = _out1880;
              _4738_recIdents = _out1881;
              r = ((_4736_onExpr).Sel(DCOMP.__default.escapeName(_4734_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4739_typ;
              RAST._IType _out1882;
              _out1882 = (this).GenType(_4731_fieldType, false, false);
              _4739_typ = _out1882;
              if (((_4739_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1883;
                DCOMP._IOwnership _out1884;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1883, out _out1884);
                r = _out1883;
                resultingOwnership = _out1884;
              }
              readIdents = _4738_recIdents;
            } else {
              RAST._IExpr _4740_onExpr;
              DCOMP._IOwnership _4741_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4742_recIdents;
              RAST._IExpr _out1885;
              DCOMP._IOwnership _out1886;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1887;
              (this).GenExpr(_4735_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1885, out _out1886, out _out1887);
              _4740_onExpr = _out1885;
              _4741_onOwned = _out1886;
              _4742_recIdents = _out1887;
              r = _4740_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4734_field));
              if (_4733_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4743_s;
                _4743_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4740_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4734_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4743_s);
              }
              DCOMP._IOwnership _4744_fromOwnership;
              _4744_fromOwnership = ((_4733_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1888;
              DCOMP._IOwnership _out1889;
              DCOMP.COMP.FromOwnership(r, _4744_fromOwnership, expectedOwnership, out _out1888, out _out1889);
              r = _out1888;
              resultingOwnership = _out1889;
              readIdents = _4742_recIdents;
            }
            return ;
          }
        } else {
          DAST._IExpression _4745___mcc_h235 = _source174.dtor_lo;
          DAST._IExpression _4746___mcc_h236 = _source174.dtor_hi;
          DAST._IType _4747_fieldType = _4099___mcc_h52;
          bool _4748_isDatatype = _4098___mcc_h51;
          bool _4749_isConstant = _4097___mcc_h50;
          Dafny.ISequence<Dafny.Rune> _4750_field = _4096___mcc_h49;
          DAST._IExpression _4751_on = _4095___mcc_h48;
          {
            if (_4748_isDatatype) {
              RAST._IExpr _4752_onExpr;
              DCOMP._IOwnership _4753_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4754_recIdents;
              RAST._IExpr _out1890;
              DCOMP._IOwnership _out1891;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1892;
              (this).GenExpr(_4751_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1890, out _out1891, out _out1892);
              _4752_onExpr = _out1890;
              _4753_onOwned = _out1891;
              _4754_recIdents = _out1892;
              r = ((_4752_onExpr).Sel(DCOMP.__default.escapeName(_4750_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _4755_typ;
              RAST._IType _out1893;
              _out1893 = (this).GenType(_4747_fieldType, false, false);
              _4755_typ = _out1893;
              if (((_4755_typ).CanReadWithoutClone()) && ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())))) {
                resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
              } else {
                RAST._IExpr _out1894;
                DCOMP._IOwnership _out1895;
                DCOMP.COMP.FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out1894, out _out1895);
                r = _out1894;
                resultingOwnership = _out1895;
              }
              readIdents = _4754_recIdents;
            } else {
              RAST._IExpr _4756_onExpr;
              DCOMP._IOwnership _4757_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4758_recIdents;
              RAST._IExpr _out1896;
              DCOMP._IOwnership _out1897;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1898;
              (this).GenExpr(_4751_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1896, out _out1897, out _out1898);
              _4756_onExpr = _out1896;
              _4757_onOwned = _out1897;
              _4758_recIdents = _out1898;
              r = _4756_onExpr;
              r = (r).Sel(DCOMP.__default.escapeName(_4750_field));
              if (_4749_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                Dafny.ISequence<Dafny.Rune> _4759_s;
                _4759_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), (_4756_onExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), DCOMP.__default.escapeName(_4750_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
                r = RAST.Expr.create_RawExpr(_4759_s);
              }
              DCOMP._IOwnership _4760_fromOwnership;
              _4760_fromOwnership = ((_4749_isConstant) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed()));
              RAST._IExpr _out1899;
              DCOMP._IOwnership _out1900;
              DCOMP.COMP.FromOwnership(r, _4760_fromOwnership, expectedOwnership, out _out1899, out _out1900);
              r = _out1899;
              resultingOwnership = _out1900;
              readIdents = _4758_recIdents;
            }
            return ;
          }
        }
      } else if (_source171.is_SelectFn) {
        DAST._IExpression _4761___mcc_h239 = _source171.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _4762___mcc_h240 = _source171.dtor_field;
        bool _4763___mcc_h241 = _source171.dtor_onDatatype;
        bool _4764___mcc_h242 = _source171.dtor_isStatic;
        BigInteger _4765___mcc_h243 = _source171.dtor_arity;
        BigInteger _4766_arity = _4765___mcc_h243;
        bool _4767_isStatic = _4764___mcc_h242;
        bool _4768_isDatatype = _4763___mcc_h241;
        Dafny.ISequence<Dafny.Rune> _4769_field = _4762___mcc_h240;
        DAST._IExpression _4770_on = _4761___mcc_h239;
        {
          RAST._IExpr _4771_onExpr;
          DCOMP._IOwnership _4772_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4773_recIdents;
          RAST._IExpr _out1901;
          DCOMP._IOwnership _out1902;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1903;
          (this).GenExpr(_4770_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1901, out _out1902, out _out1903);
          _4771_onExpr = _out1901;
          _4772_onOwned = _out1902;
          _4773_recIdents = _out1903;
          Dafny.ISequence<Dafny.Rune> _4774_s = Dafny.Sequence<Dafny.Rune>.Empty;
          Dafny.ISequence<Dafny.Rune> _4775_onString;
          _4775_onString = (_4771_onExpr)._ToString(DCOMP.__default.IND);
          if (_4767_isStatic) {
            _4774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4775_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_4769_field));
          } else {
            _4774_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            _4774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _4775_onString), ((object.Equals(_4772_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _4776_args;
            _4776_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _4777_i;
            _4777_i = BigInteger.Zero;
            while ((_4777_i) < (_4766_arity)) {
              if ((_4777_i).Sign == 1) {
                _4776_args = Dafny.Sequence<Dafny.Rune>.Concat(_4776_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _4776_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4776_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_4777_i));
              _4777_i = (_4777_i) + (BigInteger.One);
            }
            _4774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _4776_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            _4774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_4769_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _4776_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            _4774_s = Dafny.Sequence<Dafny.Rune>.Concat(_4774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _4774_s = Dafny.Sequence<Dafny.Rune>.Concat(_4774_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          Dafny.ISequence<Dafny.Rune> _4778_typeShape;
          _4778_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
          BigInteger _4779_i;
          _4779_i = BigInteger.Zero;
          while ((_4779_i) < (_4766_arity)) {
            if ((_4779_i).Sign == 1) {
              _4778_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4778_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            _4778_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4778_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
            _4779_i = (_4779_i) + (BigInteger.One);
          }
          _4778_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_4778_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
          _4774_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _4774_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _4778_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          r = RAST.Expr.create_RawExpr(_4774_s);
          RAST._IExpr _out1904;
          DCOMP._IOwnership _out1905;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1904, out _out1905);
          r = _out1904;
          resultingOwnership = _out1905;
          readIdents = _4773_recIdents;
          return ;
        }
      } else if (_source171.is_Index) {
        DAST._IExpression _4780___mcc_h244 = _source171.dtor_expr;
        DAST._ICollKind _4781___mcc_h245 = _source171.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _4782___mcc_h246 = _source171.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _4783_indices = _4782___mcc_h246;
        DAST._ICollKind _4784_collKind = _4781___mcc_h245;
        DAST._IExpression _4785_on = _4780___mcc_h244;
        {
          RAST._IExpr _4786_onExpr;
          DCOMP._IOwnership _4787_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4788_recIdents;
          RAST._IExpr _out1906;
          DCOMP._IOwnership _out1907;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1908;
          (this).GenExpr(_4785_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1906, out _out1907, out _out1908);
          _4786_onExpr = _out1906;
          _4787_onOwned = _out1907;
          _4788_recIdents = _out1908;
          readIdents = _4788_recIdents;
          r = _4786_onExpr;
          BigInteger _4789_i;
          _4789_i = BigInteger.Zero;
          while ((_4789_i) < (new BigInteger((_4783_indices).Count))) {
            if (object.Equals(_4784_collKind, DAST.CollKind.create_Array())) {
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IExpr _4790_idx;
            DCOMP._IOwnership _4791_idxOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4792_recIdentsIdx;
            RAST._IExpr _out1909;
            DCOMP._IOwnership _out1910;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1911;
            (this).GenExpr((_4783_indices).Select(_4789_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1909, out _out1910, out _out1911);
            _4790_idx = _out1909;
            _4791_idxOwned = _out1910;
            _4792_recIdentsIdx = _out1911;
            r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_4790_idx);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4792_recIdentsIdx);
            _4789_i = (_4789_i) + (BigInteger.One);
          }
          RAST._IExpr _out1912;
          DCOMP._IOwnership _out1913;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1912, out _out1913);
          r = _out1912;
          resultingOwnership = _out1913;
          return ;
        }
      } else if (_source171.is_IndexRange) {
        DAST._IExpression _4793___mcc_h247 = _source171.dtor_expr;
        bool _4794___mcc_h248 = _source171.dtor_isArray;
        Std.Wrappers._IOption<DAST._IExpression> _4795___mcc_h249 = _source171.dtor_low;
        Std.Wrappers._IOption<DAST._IExpression> _4796___mcc_h250 = _source171.dtor_high;
        Std.Wrappers._IOption<DAST._IExpression> _4797_high = _4796___mcc_h250;
        Std.Wrappers._IOption<DAST._IExpression> _4798_low = _4795___mcc_h249;
        bool _4799_isArray = _4794___mcc_h248;
        DAST._IExpression _4800_on = _4793___mcc_h247;
        {
          RAST._IExpr _4801_onExpr;
          DCOMP._IOwnership _4802_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4803_recIdents;
          RAST._IExpr _out1914;
          DCOMP._IOwnership _out1915;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1916;
          (this).GenExpr(_4800_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1914, out _out1915, out _out1916);
          _4801_onExpr = _out1914;
          _4802_onOwned = _out1915;
          _4803_recIdents = _out1916;
          readIdents = _4803_recIdents;
          Dafny.ISequence<Dafny.Rune> _4804_methodName;
          _4804_methodName = (((_4798_low).is_Some) ? ((((_4797_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_4797_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
          Dafny.ISequence<RAST._IExpr> _4805_arguments;
          _4805_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
          Std.Wrappers._IOption<DAST._IExpression> _source175 = _4798_low;
          if (_source175.is_None) {
          } else {
            DAST._IExpression _4806___mcc_h280 = _source175.dtor_value;
            DAST._IExpression _4807_l = _4806___mcc_h280;
            {
              RAST._IExpr _4808_lExpr;
              DCOMP._IOwnership _4809___v135;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4810_recIdentsL;
              RAST._IExpr _out1917;
              DCOMP._IOwnership _out1918;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1919;
              (this).GenExpr(_4807_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1917, out _out1918, out _out1919);
              _4808_lExpr = _out1917;
              _4809___v135 = _out1918;
              _4810_recIdentsL = _out1919;
              _4805_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4805_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4808_lExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4810_recIdentsL);
            }
          }
          Std.Wrappers._IOption<DAST._IExpression> _source176 = _4797_high;
          if (_source176.is_None) {
          } else {
            DAST._IExpression _4811___mcc_h281 = _source176.dtor_value;
            DAST._IExpression _4812_h = _4811___mcc_h281;
            {
              RAST._IExpr _4813_hExpr;
              DCOMP._IOwnership _4814___v136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4815_recIdentsH;
              RAST._IExpr _out1920;
              DCOMP._IOwnership _out1921;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1922;
              (this).GenExpr(_4812_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1920, out _out1921, out _out1922);
              _4813_hExpr = _out1920;
              _4814___v136 = _out1921;
              _4815_recIdentsH = _out1922;
              _4805_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_4805_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_4813_hExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4815_recIdentsH);
            }
          }
          r = _4801_onExpr;
          if (_4799_isArray) {
            if (!(_4804_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              _4804_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _4804_methodName);
            }
            r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _4804_methodName))).Apply(_4805_arguments);
          } else {
            if (!(_4804_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
              r = ((r).Sel(_4804_methodName)).Apply(_4805_arguments);
            }
          }
          RAST._IExpr _out1923;
          DCOMP._IOwnership _out1924;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1923, out _out1924);
          r = _out1923;
          resultingOwnership = _out1924;
          return ;
        }
      } else if (_source171.is_TupleSelect) {
        DAST._IExpression _4816___mcc_h251 = _source171.dtor_expr;
        BigInteger _4817___mcc_h252 = _source171.dtor_index;
        DAST._IType _4818___mcc_h253 = _source171.dtor_fieldType;
        DAST._IType _4819_fieldType = _4818___mcc_h253;
        BigInteger _4820_idx = _4817___mcc_h252;
        DAST._IExpression _4821_on = _4816___mcc_h251;
        {
          RAST._IExpr _4822_onExpr;
          DCOMP._IOwnership _4823_onOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4824_recIdents;
          RAST._IExpr _out1925;
          DCOMP._IOwnership _out1926;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1927;
          (this).GenExpr(_4821_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1925, out _out1926, out _out1927);
          _4822_onExpr = _out1925;
          _4823_onOwnership = _out1926;
          _4824_recIdents = _out1927;
          Dafny.ISequence<Dafny.Rune> _4825_selName;
          _4825_selName = Std.Strings.__default.OfNat(_4820_idx);
          DAST._IType _source177 = _4819_fieldType;
          if (_source177.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4826___mcc_h282 = _source177.dtor_Path_i_a0;
            Dafny.ISequence<DAST._IType> _4827___mcc_h283 = _source177.dtor_typeArgs;
            DAST._IResolvedType _4828___mcc_h284 = _source177.dtor_resolved;
          } else if (_source177.is_Nullable) {
            DAST._IType _4829___mcc_h288 = _source177.dtor_Nullable_i_a0;
          } else if (_source177.is_Tuple) {
            Dafny.ISequence<DAST._IType> _4830___mcc_h290 = _source177.dtor_Tuple_i_a0;
            Dafny.ISequence<DAST._IType> _4831_tps = _4830___mcc_h290;
            if (((_4819_fieldType).is_Tuple) && ((new BigInteger((_4831_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
              _4825_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _4825_selName);
            }
          } else if (_source177.is_Array) {
            DAST._IType _4832___mcc_h292 = _source177.dtor_element;
            BigInteger _4833___mcc_h293 = _source177.dtor_dims;
          } else if (_source177.is_Seq) {
            DAST._IType _4834___mcc_h296 = _source177.dtor_element;
          } else if (_source177.is_Set) {
            DAST._IType _4835___mcc_h298 = _source177.dtor_element;
          } else if (_source177.is_Multiset) {
            DAST._IType _4836___mcc_h300 = _source177.dtor_element;
          } else if (_source177.is_Map) {
            DAST._IType _4837___mcc_h302 = _source177.dtor_key;
            DAST._IType _4838___mcc_h303 = _source177.dtor_value;
          } else if (_source177.is_SetBuilder) {
            DAST._IType _4839___mcc_h306 = _source177.dtor_element;
          } else if (_source177.is_MapBuilder) {
            DAST._IType _4840___mcc_h308 = _source177.dtor_key;
            DAST._IType _4841___mcc_h309 = _source177.dtor_value;
          } else if (_source177.is_Arrow) {
            Dafny.ISequence<DAST._IType> _4842___mcc_h312 = _source177.dtor_args;
            DAST._IType _4843___mcc_h313 = _source177.dtor_result;
          } else if (_source177.is_Primitive) {
            DAST._IPrimitive _4844___mcc_h316 = _source177.dtor_Primitive_i_a0;
          } else if (_source177.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _4845___mcc_h318 = _source177.dtor_Passthrough_i_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _4846___mcc_h320 = _source177.dtor_TypeArg_i_a0;
          }
          r = (_4822_onExpr).Sel(_4825_selName);
          RAST._IExpr _out1928;
          DCOMP._IOwnership _out1929;
          DCOMP.COMP.FromOwnership(r, _4823_onOwnership, expectedOwnership, out _out1928, out _out1929);
          r = _out1928;
          resultingOwnership = _out1929;
          readIdents = _4824_recIdents;
          return ;
        }
      } else if (_source171.is_Call) {
        DAST._IExpression _4847___mcc_h254 = _source171.dtor_on;
        DAST._ICallName _4848___mcc_h255 = _source171.dtor_callName;
        Dafny.ISequence<DAST._IType> _4849___mcc_h256 = _source171.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _4850___mcc_h257 = _source171.dtor_args;
        Dafny.ISequence<DAST._IExpression> _4851_args = _4850___mcc_h257;
        Dafny.ISequence<DAST._IType> _4852_typeArgs = _4849___mcc_h256;
        DAST._ICallName _4853_name = _4848___mcc_h255;
        DAST._IExpression _4854_on = _4847___mcc_h254;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          RAST._IExpr _4855_onExpr;
          DCOMP._IOwnership _4856___v138;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4857_recIdents;
          RAST._IExpr _out1930;
          DCOMP._IOwnership _out1931;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1932;
          (this).GenExpr(_4854_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out1930, out _out1931, out _out1932);
          _4855_onExpr = _out1930;
          _4856___v138 = _out1931;
          _4857_recIdents = _out1932;
          Dafny.ISequence<RAST._IType> _4858_typeExprs;
          _4858_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
          if ((new BigInteger((_4852_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _hi35 = new BigInteger((_4852_typeArgs).Count);
            for (BigInteger _4859_typeI = BigInteger.Zero; _4859_typeI < _hi35; _4859_typeI++) {
              RAST._IType _4860_typeExpr;
              RAST._IType _out1933;
              _out1933 = (this).GenType((_4852_typeArgs).Select(_4859_typeI), false, false);
              _4860_typeExpr = _out1933;
              _4858_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_4858_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_4860_typeExpr));
            }
          }
          Dafny.ISequence<RAST._IExpr> _4861_argExprs;
          _4861_argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi36 = new BigInteger((_4851_args).Count);
          for (BigInteger _4862_i = BigInteger.Zero; _4862_i < _hi36; _4862_i++) {
            DCOMP._IOwnership _4863_argOwnership;
            _4863_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            if (((_4853_name).is_CallName) && ((_4862_i) < (new BigInteger((((_4853_name).dtor_signature)).Count)))) {
              RAST._IType _4864_tpe;
              RAST._IType _out1934;
              _out1934 = (this).GenType(((((_4853_name).dtor_signature)).Select(_4862_i)).dtor_typ, false, false);
              _4864_tpe = _out1934;
              if ((_4864_tpe).CanReadWithoutClone()) {
                _4863_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
              }
            }
            RAST._IExpr _4865_argExpr;
            DCOMP._IOwnership _4866___v139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4867_argIdents;
            RAST._IExpr _out1935;
            DCOMP._IOwnership _out1936;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1937;
            (this).GenExpr((_4851_args).Select(_4862_i), selfIdent, env, _4863_argOwnership, out _out1935, out _out1936, out _out1937);
            _4865_argExpr = _out1935;
            _4866___v139 = _out1936;
            _4867_argIdents = _out1937;
            _4861_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(_4861_argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_4865_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4867_argIdents);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _4857_recIdents);
          Dafny.ISequence<Dafny.Rune> _4868_renderedName;
          _4868_renderedName = ((System.Func<DAST._ICallName, Dafny.ISequence<Dafny.Rune>>)((_source178) => {
            if (_source178.is_CallName) {
              Dafny.ISequence<Dafny.Rune> _4869___mcc_h322 = _source178.dtor_name;
              Std.Wrappers._IOption<DAST._IType> _4870___mcc_h323 = _source178.dtor_onType;
              Dafny.ISequence<DAST._IFormal> _4871___mcc_h324 = _source178.dtor_signature;
              Dafny.ISequence<Dafny.Rune> _4872_ident = _4869___mcc_h322;
              return DCOMP.__default.escapeName(_4872_ident);
            } else if (_source178.is_MapBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else if (_source178.is_MapBuilderBuild) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            } else if (_source178.is_SetBuilderAdd) {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
            }
          }))(_4853_name);
          DAST._IExpression _source179 = _4854_on;
          if (_source179.is_Literal) {
            DAST._ILiteral _4873___mcc_h325 = _source179.dtor_Literal_i_a0;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _4874___mcc_h327 = _source179.dtor_Ident_i_a0;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4875___mcc_h329 = _source179.dtor_Companion_i_a0;
            {
              _4855_onExpr = (_4855_onExpr).MSel(_4868_renderedName);
            }
          } else if (_source179.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _4876___mcc_h331 = _source179.dtor_Tuple_i_a0;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4877___mcc_h333 = _source179.dtor_path;
            Dafny.ISequence<DAST._IType> _4878___mcc_h334 = _source179.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _4879___mcc_h335 = _source179.dtor_args;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _4880___mcc_h339 = _source179.dtor_dims;
            DAST._IType _4881___mcc_h340 = _source179.dtor_typ;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_DatatypeValue) {
            DAST._IDatatypeType _4882___mcc_h343 = _source179.dtor_datatypeType;
            Dafny.ISequence<DAST._IType> _4883___mcc_h344 = _source179.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _4884___mcc_h345 = _source179.dtor_variant;
            bool _4885___mcc_h346 = _source179.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _4886___mcc_h347 = _source179.dtor_contents;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_Convert) {
            DAST._IExpression _4887___mcc_h353 = _source179.dtor_value;
            DAST._IType _4888___mcc_h354 = _source179.dtor_from;
            DAST._IType _4889___mcc_h355 = _source179.dtor_typ;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_SeqConstruct) {
            DAST._IExpression _4890___mcc_h359 = _source179.dtor_length;
            DAST._IExpression _4891___mcc_h360 = _source179.dtor_elem;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _4892___mcc_h363 = _source179.dtor_elements;
            DAST._IType _4893___mcc_h364 = _source179.dtor_typ;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _4894___mcc_h367 = _source179.dtor_elements;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_MultisetValue) {
            Dafny.ISequence<DAST._IExpression> _4895___mcc_h369 = _source179.dtor_elements;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _4896___mcc_h371 = _source179.dtor_mapElems;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_MapBuilder) {
            DAST._IType _4897___mcc_h373 = _source179.dtor_keyType;
            DAST._IType _4898___mcc_h374 = _source179.dtor_valueType;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_SeqUpdate) {
            DAST._IExpression _4899___mcc_h377 = _source179.dtor_expr;
            DAST._IExpression _4900___mcc_h378 = _source179.dtor_indexExpr;
            DAST._IExpression _4901___mcc_h379 = _source179.dtor_value;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_MapUpdate) {
            DAST._IExpression _4902___mcc_h383 = _source179.dtor_expr;
            DAST._IExpression _4903___mcc_h384 = _source179.dtor_indexExpr;
            DAST._IExpression _4904___mcc_h385 = _source179.dtor_value;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_SetBuilder) {
            DAST._IType _4905___mcc_h389 = _source179.dtor_elemType;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_ToMultiset) {
            DAST._IExpression _4906___mcc_h391 = _source179.dtor_ToMultiset_i_a0;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_This) {
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_Ite) {
            DAST._IExpression _4907___mcc_h393 = _source179.dtor_cond;
            DAST._IExpression _4908___mcc_h394 = _source179.dtor_thn;
            DAST._IExpression _4909___mcc_h395 = _source179.dtor_els;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_UnOp) {
            DAST._IUnaryOp _4910___mcc_h399 = _source179.dtor_unOp;
            DAST._IExpression _4911___mcc_h400 = _source179.dtor_expr;
            DAST.Format._IUnaryOpFormat _4912___mcc_h401 = _source179.dtor_format1;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_BinOp) {
            DAST._IBinOp _4913___mcc_h405 = _source179.dtor_op;
            DAST._IExpression _4914___mcc_h406 = _source179.dtor_left;
            DAST._IExpression _4915___mcc_h407 = _source179.dtor_right;
            DAST.Format._IBinaryOpFormat _4916___mcc_h408 = _source179.dtor_format2;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_ArrayLen) {
            DAST._IExpression _4917___mcc_h413 = _source179.dtor_expr;
            BigInteger _4918___mcc_h414 = _source179.dtor_dim;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_MapKeys) {
            DAST._IExpression _4919___mcc_h417 = _source179.dtor_expr;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_MapValues) {
            DAST._IExpression _4920___mcc_h419 = _source179.dtor_expr;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_Select) {
            DAST._IExpression _4921___mcc_h421 = _source179.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4922___mcc_h422 = _source179.dtor_field;
            bool _4923___mcc_h423 = _source179.dtor_isConstant;
            bool _4924___mcc_h424 = _source179.dtor_onDatatype;
            DAST._IType _4925___mcc_h425 = _source179.dtor_fieldType;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_SelectFn) {
            DAST._IExpression _4926___mcc_h431 = _source179.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _4927___mcc_h432 = _source179.dtor_field;
            bool _4928___mcc_h433 = _source179.dtor_onDatatype;
            bool _4929___mcc_h434 = _source179.dtor_isStatic;
            BigInteger _4930___mcc_h435 = _source179.dtor_arity;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_Index) {
            DAST._IExpression _4931___mcc_h441 = _source179.dtor_expr;
            DAST._ICollKind _4932___mcc_h442 = _source179.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _4933___mcc_h443 = _source179.dtor_indices;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_IndexRange) {
            DAST._IExpression _4934___mcc_h447 = _source179.dtor_expr;
            bool _4935___mcc_h448 = _source179.dtor_isArray;
            Std.Wrappers._IOption<DAST._IExpression> _4936___mcc_h449 = _source179.dtor_low;
            Std.Wrappers._IOption<DAST._IExpression> _4937___mcc_h450 = _source179.dtor_high;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_TupleSelect) {
            DAST._IExpression _4938___mcc_h455 = _source179.dtor_expr;
            BigInteger _4939___mcc_h456 = _source179.dtor_index;
            DAST._IType _4940___mcc_h457 = _source179.dtor_fieldType;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_Call) {
            DAST._IExpression _4941___mcc_h461 = _source179.dtor_on;
            DAST._ICallName _4942___mcc_h462 = _source179.dtor_callName;
            Dafny.ISequence<DAST._IType> _4943___mcc_h463 = _source179.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _4944___mcc_h464 = _source179.dtor_args;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _4945___mcc_h469 = _source179.dtor_params;
            DAST._IType _4946___mcc_h470 = _source179.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _4947___mcc_h471 = _source179.dtor_body;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4948___mcc_h475 = _source179.dtor_values;
            DAST._IType _4949___mcc_h476 = _source179.dtor_retType;
            DAST._IExpression _4950___mcc_h477 = _source179.dtor_expr;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _4951___mcc_h481 = _source179.dtor_name;
            DAST._IType _4952___mcc_h482 = _source179.dtor_typ;
            DAST._IExpression _4953___mcc_h483 = _source179.dtor_value;
            DAST._IExpression _4954___mcc_h484 = _source179.dtor_iifeBody;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_Apply) {
            DAST._IExpression _4955___mcc_h489 = _source179.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _4956___mcc_h490 = _source179.dtor_args;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_TypeTest) {
            DAST._IExpression _4957___mcc_h493 = _source179.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4958___mcc_h494 = _source179.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _4959___mcc_h495 = _source179.dtor_variant;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_InitializationValue) {
            DAST._IType _4960___mcc_h499 = _source179.dtor_typ;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_BoolBoundedPool) {
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_SetBoundedPool) {
            DAST._IExpression _4961___mcc_h501 = _source179.dtor_of;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else if (_source179.is_SeqBoundedPool) {
            DAST._IExpression _4962___mcc_h503 = _source179.dtor_of;
            bool _4963___mcc_h504 = _source179.dtor_includeDuplicates;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          } else {
            DAST._IExpression _4964___mcc_h507 = _source179.dtor_lo;
            DAST._IExpression _4965___mcc_h508 = _source179.dtor_hi;
            {
              _4855_onExpr = (_4855_onExpr).Sel(_4868_renderedName);
            }
          }
          r = _4855_onExpr;
          if ((new BigInteger((_4858_typeExprs).Count)).Sign == 1) {
            r = (r).ApplyType(_4858_typeExprs);
          }
          r = (r).Apply(_4861_argExprs);
          RAST._IExpr _out1938;
          DCOMP._IOwnership _out1939;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1938, out _out1939);
          r = _out1938;
          resultingOwnership = _out1939;
          return ;
        }
      } else if (_source171.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _4966___mcc_h258 = _source171.dtor_params;
        DAST._IType _4967___mcc_h259 = _source171.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _4968___mcc_h260 = _source171.dtor_body;
        Dafny.ISequence<DAST._IStatement> _4969_body = _4968___mcc_h260;
        DAST._IType _4970_retType = _4967___mcc_h259;
        Dafny.ISequence<DAST._IFormal> _4971_paramsDafny = _4966___mcc_h258;
        {
          Dafny.ISequence<RAST._IFormal> _4972_params;
          Dafny.ISequence<RAST._IFormal> _out1940;
          _out1940 = (this).GenParams(_4971_paramsDafny);
          _4972_params = _out1940;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4973_paramNames;
          _4973_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _4974_paramTypesMap;
          _4974_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          BigInteger _hi37 = new BigInteger((_4972_params).Count);
          for (BigInteger _4975_i = BigInteger.Zero; _4975_i < _hi37; _4975_i++) {
            Dafny.ISequence<Dafny.Rune> _4976_name;
            _4976_name = ((_4972_params).Select(_4975_i)).dtor_name;
            _4973_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_4973_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_4976_name));
            _4974_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_4974_paramTypesMap, _4976_name, ((_4972_params).Select(_4975_i)).dtor_tpe);
          }
          DCOMP._IEnvironment _4977_env;
          _4977_env = DCOMP.Environment.create(_4973_paramNames, _4974_paramTypesMap);
          RAST._IExpr _4978_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4979_recIdents;
          DCOMP._IEnvironment _4980___v144;
          RAST._IExpr _out1941;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1942;
          DCOMP._IEnvironment _out1943;
          (this).GenStmts(_4969_body, ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), _4977_env, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out1941, out _out1942, out _out1943);
          _4978_recursiveGen = _out1941;
          _4979_recIdents = _out1942;
          _4980___v144 = _out1943;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          _4979_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4979_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_4981_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
            var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
            foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_4981_paramNames).CloneAsArray()) {
              Dafny.ISequence<Dafny.Rune> _4982_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
              if ((_4981_paramNames).Contains(_4982_name)) {
                _coll6.Add(_4982_name);
              }
            }
            return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
          }))())(_4973_paramNames));
          RAST._IExpr _4983_allReadCloned;
          _4983_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          while (!(_4979_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _4984_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_4979_recIdents).Elements) {
              _4984_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
              if ((_4979_recIdents).Contains(_4984_next)) {
                goto after__ASSIGN_SUCH_THAT_3;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 3629)");
          after__ASSIGN_SUCH_THAT_3: ;
            if ((!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) && ((_4984_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
              if (!object.Equals(selfIdent, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())) {
                _4983_allReadCloned = (_4983_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              }
            } else if (!((_4973_paramNames).Contains(_4984_next))) {
              _4983_allReadCloned = (_4983_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _4984_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(_4984_next)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4984_next));
            }
            _4979_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_4979_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4984_next));
          }
          RAST._IType _4985_retTypeGen;
          RAST._IType _out1944;
          _out1944 = (this).GenType(_4970_retType, false, true);
          _4985_retTypeGen = _out1944;
          r = RAST.Expr.create_Block((_4983_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_4972_params, Std.Wrappers.Option<RAST._IType>.create_Some(_4985_retTypeGen), RAST.Expr.create_Block(_4978_recursiveGen)))));
          RAST._IExpr _out1945;
          DCOMP._IOwnership _out1946;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1945, out _out1946);
          r = _out1945;
          resultingOwnership = _out1946;
          return ;
        }
      } else if (_source171.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4986___mcc_h261 = _source171.dtor_values;
        DAST._IType _4987___mcc_h262 = _source171.dtor_retType;
        DAST._IExpression _4988___mcc_h263 = _source171.dtor_expr;
        DAST._IExpression _4989_expr = _4988___mcc_h263;
        DAST._IType _4990_retType = _4987___mcc_h262;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _4991_values = _4986___mcc_h261;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4992_paramNames;
          _4992_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<RAST._IFormal> _4993_paramFormals;
          Dafny.ISequence<RAST._IFormal> _out1947;
          _out1947 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_4994_value) => {
            return (_4994_value).dtor__0;
          })), _4991_values));
          _4993_paramFormals = _out1947;
          Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _4995_paramTypes;
          _4995_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _4996_paramNamesSet;
          _4996_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _hi38 = new BigInteger((_4991_values).Count);
          for (BigInteger _4997_i = BigInteger.Zero; _4997_i < _hi38; _4997_i++) {
            Dafny.ISequence<Dafny.Rune> _4998_name;
            _4998_name = (((_4991_values).Select(_4997_i)).dtor__0).dtor_name;
            Dafny.ISequence<Dafny.Rune> _4999_rName;
            _4999_rName = DCOMP.__default.escapeName(_4998_name);
            _4992_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_4992_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_4999_rName));
            _4995_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_4995_paramTypes, _4999_rName, ((_4993_paramFormals).Select(_4997_i)).dtor_tpe);
            _4996_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_4996_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_4999_rName));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          BigInteger _hi39 = new BigInteger((_4991_values).Count);
          for (BigInteger _5000_i = BigInteger.Zero; _5000_i < _hi39; _5000_i++) {
            RAST._IType _5001_typeGen;
            RAST._IType _out1948;
            _out1948 = (this).GenType((((_4991_values).Select(_5000_i)).dtor__0).dtor_typ, false, true);
            _5001_typeGen = _out1948;
            RAST._IExpr _5002_valueGen;
            DCOMP._IOwnership _5003___v145;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5004_recIdents;
            RAST._IExpr _out1949;
            DCOMP._IOwnership _out1950;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1951;
            (this).GenExpr(((_4991_values).Select(_5000_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1949, out _out1950, out _out1951);
            _5002_valueGen = _out1949;
            _5003___v145 = _out1950;
            _5004_recIdents = _out1951;
            r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_4991_values).Select(_5000_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_5001_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5002_valueGen)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _5004_recIdents);
          }
          DCOMP._IEnvironment _5005_newEnv;
          _5005_newEnv = DCOMP.Environment.create(_4992_paramNames, _4995_paramTypes);
          RAST._IExpr _5006_recGen;
          DCOMP._IOwnership _5007_recOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5008_recIdents;
          RAST._IExpr _out1952;
          DCOMP._IOwnership _out1953;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1954;
          (this).GenExpr(_4989_expr, selfIdent, _5005_newEnv, expectedOwnership, out _out1952, out _out1953, out _out1954);
          _5006_recGen = _out1952;
          _5007_recOwned = _out1953;
          _5008_recIdents = _out1954;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5008_recIdents, _4996_paramNamesSet);
          r = RAST.Expr.create_Block((r).Then(_5006_recGen));
          RAST._IExpr _out1955;
          DCOMP._IOwnership _out1956;
          DCOMP.COMP.FromOwnership(r, _5007_recOwned, expectedOwnership, out _out1955, out _out1956);
          r = _out1955;
          resultingOwnership = _out1956;
          return ;
        }
      } else if (_source171.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _5009___mcc_h264 = _source171.dtor_name;
        DAST._IType _5010___mcc_h265 = _source171.dtor_typ;
        DAST._IExpression _5011___mcc_h266 = _source171.dtor_value;
        DAST._IExpression _5012___mcc_h267 = _source171.dtor_iifeBody;
        DAST._IExpression _5013_iifeBody = _5012___mcc_h267;
        DAST._IExpression _5014_value = _5011___mcc_h266;
        DAST._IType _5015_tpe = _5010___mcc_h265;
        Dafny.ISequence<Dafny.Rune> _5016_name = _5009___mcc_h264;
        {
          RAST._IExpr _5017_valueGen;
          DCOMP._IOwnership _5018___v146;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5019_recIdents;
          RAST._IExpr _out1957;
          DCOMP._IOwnership _out1958;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1959;
          (this).GenExpr(_5014_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1957, out _out1958, out _out1959);
          _5017_valueGen = _out1957;
          _5018___v146 = _out1958;
          _5019_recIdents = _out1959;
          readIdents = _5019_recIdents;
          RAST._IType _5020_valueTypeGen;
          RAST._IType _out1960;
          _out1960 = (this).GenType(_5015_tpe, false, true);
          _5020_valueTypeGen = _out1960;
          RAST._IExpr _5021_bodyGen;
          DCOMP._IOwnership _5022___v147;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5023_bodyIdents;
          RAST._IExpr _out1961;
          DCOMP._IOwnership _out1962;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1963;
          (this).GenExpr(_5013_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1961, out _out1962, out _out1963);
          _5021_bodyGen = _out1961;
          _5022___v147 = _out1962;
          _5023_bodyIdents = _out1963;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_5023_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_5016_name)))));
          r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_5016_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_5020_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5017_valueGen))).Then(_5021_bodyGen));
          RAST._IExpr _out1964;
          DCOMP._IOwnership _out1965;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1964, out _out1965);
          r = _out1964;
          resultingOwnership = _out1965;
          return ;
        }
      } else if (_source171.is_Apply) {
        DAST._IExpression _5024___mcc_h268 = _source171.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _5025___mcc_h269 = _source171.dtor_args;
        Dafny.ISequence<DAST._IExpression> _5026_args = _5025___mcc_h269;
        DAST._IExpression _5027_func = _5024___mcc_h268;
        {
          RAST._IExpr _5028_funcExpr;
          DCOMP._IOwnership _5029___v148;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5030_recIdents;
          RAST._IExpr _out1966;
          DCOMP._IOwnership _out1967;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1968;
          (this).GenExpr(_5027_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1966, out _out1967, out _out1968);
          _5028_funcExpr = _out1966;
          _5029___v148 = _out1967;
          _5030_recIdents = _out1968;
          readIdents = _5030_recIdents;
          Dafny.ISequence<RAST._IExpr> _5031_rArgs;
          _5031_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi40 = new BigInteger((_5026_args).Count);
          for (BigInteger _5032_i = BigInteger.Zero; _5032_i < _hi40; _5032_i++) {
            RAST._IExpr _5033_argExpr;
            DCOMP._IOwnership _5034_argOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5035_argIdents;
            RAST._IExpr _out1969;
            DCOMP._IOwnership _out1970;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1971;
            (this).GenExpr((_5026_args).Select(_5032_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1969, out _out1970, out _out1971);
            _5033_argExpr = _out1969;
            _5034_argOwned = _out1970;
            _5035_argIdents = _out1971;
            _5031_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_5031_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_5033_argExpr));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _5035_argIdents);
          }
          r = (_5028_funcExpr).Apply(_5031_rArgs);
          RAST._IExpr _out1972;
          DCOMP._IOwnership _out1973;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1972, out _out1973);
          r = _out1972;
          resultingOwnership = _out1973;
          return ;
        }
      } else if (_source171.is_TypeTest) {
        DAST._IExpression _5036___mcc_h270 = _source171.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5037___mcc_h271 = _source171.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _5038___mcc_h272 = _source171.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _5039_variant = _5038___mcc_h272;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5040_dType = _5037___mcc_h271;
        DAST._IExpression _5041_on = _5036___mcc_h270;
        {
          RAST._IExpr _5042_exprGen;
          DCOMP._IOwnership _5043___v149;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5044_recIdents;
          RAST._IExpr _out1974;
          DCOMP._IOwnership _out1975;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1976;
          (this).GenExpr(_5041_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1974, out _out1975, out _out1976);
          _5042_exprGen = _out1974;
          _5043___v149 = _out1975;
          _5044_recIdents = _out1976;
          RAST._IType _5045_dTypePath;
          RAST._IType _out1977;
          _out1977 = DCOMP.COMP.GenPath(_5040_dType);
          _5045_dTypePath = _out1977;
          r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_5042_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_5045_dTypePath).MSel(DCOMP.__default.escapeName(_5039_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
          RAST._IExpr _out1978;
          DCOMP._IOwnership _out1979;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1978, out _out1979);
          r = _out1978;
          resultingOwnership = _out1979;
          readIdents = _5044_recIdents;
          return ;
        }
      } else if (_source171.is_InitializationValue) {
        DAST._IType _5046___mcc_h273 = _source171.dtor_typ;
        DAST._IType _5047_typ = _5046___mcc_h273;
        {
          RAST._IType _5048_typExpr;
          RAST._IType _out1980;
          _out1980 = (this).GenType(_5047_typ, false, false);
          _5048_typExpr = _out1980;
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_5048_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
          RAST._IExpr _out1981;
          DCOMP._IOwnership _out1982;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1981, out _out1982);
          r = _out1981;
          resultingOwnership = _out1982;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source171.is_BoolBoundedPool) {
        {
          r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
          RAST._IExpr _out1983;
          DCOMP._IOwnership _out1984;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1983, out _out1984);
          r = _out1983;
          resultingOwnership = _out1984;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      } else if (_source171.is_SetBoundedPool) {
        DAST._IExpression _5049___mcc_h274 = _source171.dtor_of;
        DAST._IExpression _5050_of = _5049___mcc_h274;
        {
          RAST._IExpr _5051_exprGen;
          DCOMP._IOwnership _5052___v150;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5053_recIdents;
          RAST._IExpr _out1985;
          DCOMP._IOwnership _out1986;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1987;
          (this).GenExpr(_5050_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1985, out _out1986, out _out1987);
          _5051_exprGen = _out1985;
          _5052___v150 = _out1986;
          _5053_recIdents = _out1987;
          r = ((((_5051_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          RAST._IExpr _out1988;
          DCOMP._IOwnership _out1989;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1988, out _out1989);
          r = _out1988;
          resultingOwnership = _out1989;
          readIdents = _5053_recIdents;
          return ;
        }
      } else if (_source171.is_SeqBoundedPool) {
        DAST._IExpression _5054___mcc_h275 = _source171.dtor_of;
        bool _5055___mcc_h276 = _source171.dtor_includeDuplicates;
        bool _5056_includeDuplicates = _5055___mcc_h276;
        DAST._IExpression _5057_of = _5054___mcc_h275;
        {
          RAST._IExpr _5058_exprGen;
          DCOMP._IOwnership _5059___v151;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5060_recIdents;
          RAST._IExpr _out1990;
          DCOMP._IOwnership _out1991;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1992;
          (this).GenExpr(_5057_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out1990, out _out1991, out _out1992);
          _5058_exprGen = _out1990;
          _5059___v151 = _out1991;
          _5060_recIdents = _out1992;
          r = ((_5058_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          if (!(_5056_includeDuplicates)) {
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
          }
          RAST._IExpr _out1993;
          DCOMP._IOwnership _out1994;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out1993, out _out1994);
          r = _out1993;
          resultingOwnership = _out1994;
          readIdents = _5060_recIdents;
          return ;
        }
      } else {
        DAST._IExpression _5061___mcc_h277 = _source171.dtor_lo;
        DAST._IExpression _5062___mcc_h278 = _source171.dtor_hi;
        DAST._IExpression _5063_hi = _5062___mcc_h278;
        DAST._IExpression _5064_lo = _5061___mcc_h277;
        {
          RAST._IExpr _5065_lo;
          DCOMP._IOwnership _5066___v152;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5067_recIdentsLo;
          RAST._IExpr _out1995;
          DCOMP._IOwnership _out1996;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1997;
          (this).GenExpr(_5064_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1995, out _out1996, out _out1997);
          _5065_lo = _out1995;
          _5066___v152 = _out1996;
          _5067_recIdentsLo = _out1997;
          RAST._IExpr _5068_hi;
          DCOMP._IOwnership _5069___v153;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5070_recIdentsHi;
          RAST._IExpr _out1998;
          DCOMP._IOwnership _out1999;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2000;
          (this).GenExpr(_5063_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out1998, out _out1999, out _out2000);
          _5068_hi = _out1998;
          _5069___v153 = _out1999;
          _5070_recIdentsHi = _out2000;
          r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_5065_lo, _5068_hi));
          RAST._IExpr _out2001;
          DCOMP._IOwnership _out2002;
          DCOMP.COMP.FromOwned(r, expectedOwnership, out _out2001, out _out2002);
          r = _out2001;
          resultingOwnership = _out2002;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_5067_recIdentsLo, _5070_recIdentsHi);
          return ;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _5071_i;
      _5071_i = BigInteger.Zero;
      while ((_5071_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _5072_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _5073_m;
        RAST._IMod _out2003;
        _out2003 = (this).GenModule((p).Select(_5071_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _5073_m = _out2003;
        _5072_generated = (_5073_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_5071_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _5072_generated);
        _5071_i = (_5071_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _5074_i;
      _5074_i = BigInteger.Zero;
      while ((_5074_i) < (new BigInteger((fullName).Count))) {
        if ((_5074_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_5074_i)));
        _5074_i = (_5074_i) + (BigInteger.One);
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
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
  }
} // end of namespace DCOMP